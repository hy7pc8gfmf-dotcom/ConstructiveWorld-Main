(* ===================================================================== *)
(* 模块：u5c_zeta2_sup                                                   *)
(* 使命：ζ(2) 线 GAPASUME 供件位双铸（Z2SUP01 线）。                *)
(*   ① Hws 裂项步档铸真：zb2_ia_Wsum (S J') == zb2_ia_Wsum J' + zb2_ia_W J' *)
(*      （a1_sign 终形 zb2_ia_init_bound 次前提逐字同源形）——以自铸 Q 层    *)
(*      消去律（正因子乘积消去）与逆元分配律链（Qinv_mult_distr + 单元     *)
(*      元归一）绕开 9.1 Qinv 分子刮擦 × Z.mul 卡壳（Z2A03 §二-3 登记      *)
(*      的卡壳位于此消解）。                                              *)
(*   ② Hpw 峰核机证化（按 R3 判据机证形交付·点位证书如实冻结）：           *)
(*      加权逐点封顶量 Wt n j := zb2_term n j·(j+1)·(j+2) 的——             *)
(*      加权比率恒等式（自 gapA zb2_ga_term_ratio 加权重排）、升档单调律   *)
(*      （2(j+2) ≤ n 域）、j ≤ 1 档升档律（1 ≤ n 域）、降档单调律          *)
(*      （9 ≤ n ∧ n ≤ j 域）、升降链机、与峰带归约定理：对任意 k0 满足     *)
(*      2·k0 ≤ (m+1)+6，只要峰带 [k0, m+1] 内逐点证书在句，即得全窗        *)
(*      ∀j 逐点封顶——Hpw 残余缺口由「峰带逐点证书」精确刻形（GAPASUME     *)
(*      诚实接口：残位以显式命名前提在句，语句面零承认零全局假设）。        *)
(*      峰带内点位证书需二项式尾部下界机（C(3n+1,n) ≥ (27/4)^n 型熵下界）， *)
(*      本件不铸，如实冻结申报（实测余量 3.22 倍方向见 a1 头注对照表）。    *)
(* 依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）；缓存根 S01_BaseRing、    *)
(*   S02_CauchyComplete、S03_QExp、BeukersLists；tmine04 池                *)
(*   abl_z2_itg_carrier（zb2_term/zb2_term_pos）；本池 u5c_zeta2_gapA      *)
(*   （比率律 zb2_ga_term_ratio）、u5c_zeta2_a1_sign（zb2_ia_W/zb2_ia_Wsum/ *)
(*   数值面/取消律）。零外部证书器、零实数层、零经典逻辑、零全局假设声明。  *)
(* 构造性：纯构造性、零承认式语句；语句结论全 Set 层（QleT' 为 Qle_bool    *)
(*   反映形、QeqT 为 Qeq 反映形）；量化前提均显式命名于语句内；系数不等式   *)
(*   经 nat 侧存在代换 + nia 通路（升档/降档四次型）；Q 层恒等变形经 ring   *)
(*   整式通路与假设重写通路（禁 field——本环境 Q 层 field 关系查找对含      *)
(*   应用原子目标失灵，Z2A02 §0 判例照守）；9.1 无 Qsgn、Qinv 体 match     *)
(*   Qnum（分子刮擦）照守——全部逆元面走 Qmult_inv_r/Qinv_mult_distr，     *)
(*   不展开 Qinv。                                                        *)
(* 编译配方：source Live/toolchain/env.sh && cd 沙箱/现役/abl_zeta2_pool && *)
(*   rocq c -native-compiler no -q -Q . ""                                *)
(*   -Q <绝对路径>/abl_tmine04_pool/zeta2 ""                              *)
(*   -Q <绝对路径>/vo_local_world_unified_0930 "" u5c_zeta2_sup.v         *)
(*   （三根 -Q 配平：本池/tmine04 zeta2 池/缓存根）。                      *)
(* 对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.     *)
(*   London Math. Soc. 11 (1979) 级数估计；裂项 Σ 1/(t(t+1)) 模板；        *)
(*   峰位 j* ≈ (√5−1)n/2 驻点分析（a1 头注对照：窗内归一峰值 3.106e-2，    *)
(*   常数 1/10 余量 3.22 倍）。                                            *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 Q 层基础：消去律、步档恒等式、单元平移（全假设重写通路）              *)
(* ===================================================================== *)

(* Q 层乘积消去律：k ≠ 0 且 a·k == b·k 则 a == b。
   铸法：两侧同乘 /k 后 Qmult_inv_r 归一（不展开 Qinv）。 *)
Lemma zb2_sup_qeq_cancel_r : forall a b k : Q,
  ~ (k == 0) -> (a * k == b * k)%Q -> (a == b)%Q.
Proof.
  intros a b k Hk Hab.
  assert (HC : a * k * / k == b * k * / k) by (rewrite Hab; reflexivity).
  rewrite <- !Qmult_assoc in HC.
  rewrite (Qmult_inv_r k Hk) in HC.
  rewrite !Qmult_1_r in HC.
  exact HC.
Qed.

(* 步档核心恒等式：c == a + 1 时 /a == /c + /(a·c)。
   铸法：/a 与 a·/(a·c) 同一（乘 a 后 ED 分配律链归一），再由
   /c == a·/(a·c) 与 c == a+1 合账。全部走假设重写与 ring，不触 Qinv 体。 *)
Lemma zb2_sup_qstep : forall a c : Q,
  c == a + 1 -> ~ (a == 0) -> ~ (a * c == 0) -> ~ (c == 0) -> ~ (c * a == 0) ->
  (/ a == / c + / (a * c))%Q.
Proof.
  intros a c Hca Ha Hac0 Hc0 Hca0.
  assert (H1 : / a == c * / (a * c)).
  { apply (zb2_sup_qeq_cancel_r (/ a) (c * / (a * c)) a Ha).
    assert (EC1 : / a * a == a * / a) by ring.
    assert (EC2 : c * / (a * c) * a == a * (c * / (a * c))) by ring.
    assert (EA3 : a * (c * / (a * c)) == (a * c) * / (a * c)) by ring.
    assert (EA1 : a * / a == 1) by (apply Qmult_inv_r; exact Ha).
    assert (EA2 : (a * c) * / (a * c) == 1) by (apply Qmult_inv_r; exact Hac0).
    rewrite EC1, EC2, EA3, EA1, EA2. reflexivity. }
  assert (H2 : / c == a * / (a * c)).
  { assert (ED : / (a * c) == / a * / c) by (apply Qinv_mult_distr).
    assert (EX : a * / (a * c) == a * (/ a * / c)) by (rewrite ED; reflexivity).
    assert (EY : a * (/ a * / c) == (a * / a) * / c) by ring.
    assert (EZ : a * / a == 1) by (apply Qmult_inv_r; exact Ha).
    assert (EV : (a * / a) * / c == 1 * / c) by (rewrite EZ; reflexivity).
    assert (EW : 1 * / c == / c) by (apply Qmult_1_l).
    exact (Qeq_sym _ _ (Qeq_trans _ _ _ (Qeq_trans _ _ _ (Qeq_trans _ _ _ EX EY) EV) EW)). }
  assert (EG : / c + / (a * c) == (a + 1) * / (a * c)).
  { rewrite H2.
    assert (EG1 : a * / (a * c) + / (a * c) == (a + 1) * / (a * c)) by ring.
    exact EG1. }
  apply (Qeq_trans _ (c * / (a * c)) _).
  - exact H1.
  - apply (Qeq_trans _ ((a + 1) * / (a * c)) _).
    + apply (zb2_sup_qeq_cancel_r (c * / (a * c)) ((a + 1) * / (a * c)) (a * c) Hac0).
      assert (ED1 : c * / (a * c) * (a * c) == c * ((a * c) * / (a * c))) by ring.
      assert (ED3 : (a + 1) * / (a * c) * (a * c)
                 == (a + 1) * ((a * c) * / (a * c))) by ring.
      assert (ED2 : (a * c) * / (a * c) == 1) by (apply Qmult_inv_r; exact Hac0).
      rewrite ED1, ED3, ED2.
      assert (ED4 : c * 1 == c) by (apply Qmult_1_r).
      assert (ED5 : (a + 1) * 1 == (a + 1)) by (apply Qmult_1_r).
      rewrite ED4, ED5. exact Hca.
    + exact (Qeq_sym _ _ EG).
Qed.

(* 单元平移形：/a == /c + /(a·c) 时 1 − 1/c == 1 − 1/a + 1/(a·c)
   （zb2_ia_Wsum/zb2_ia_W 形的 1/x 记法直接一致）。 *)
Lemma zb2_sup_qshift : forall a c : Q,
  (/ a == / c + / (a * c))%Q -> ((1 - 1 / c) == (1 - 1 / a) + 1 / (a * c))%Q.
Proof. intros a c H. unfold Qdiv in *. rewrite !Qmult_1_l in *. rewrite H. ring. Qed.

(* ===================================================================== *)
(* §1 Hws 裂项步档铸真（供件位一·与 a1_sign Hws 槽逐字同源）               *)
(* ===================================================================== *)

Theorem zb2_sup_Ws_step : forall J' : nat,
  zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J'.
Proof.
  intro J'. unfold zb2_ia_Wsum, zb2_ia_W.
  replace (J' + 2)%nat with (Datatypes.S (Datatypes.S J'))%nat by lia.
  apply (zb2_sup_qshift (Z.of_nat (Datatypes.S J') # 1)
                        (Z.of_nat (Datatypes.S (Datatypes.S J')) # 1)).
  apply (zb2_sup_qstep (Z.of_nat (Datatypes.S J') # 1)
                       (Z.of_nat (Datatypes.S (Datatypes.S J')) # 1)).
  - (* c == a + 1 *)
    assert (Hn : (Datatypes.S (Datatypes.S J') = Datatypes.S J' + 1)%nat) by lia.
    rewrite Hn. rewrite Nat2Z.inj_add. unfold Qeq, Qplus. cbn [Qnum Qden Qmult]. lia.
  - apply zb2_ga_pos_neq0. apply QltT_to_Qlt. apply zb2_ga_natpos_lt. lia.
  - apply zb2_ga_pos_neq0. apply Qmult_lt_0_compat; apply QltT_to_Qlt;
      apply zb2_ga_natpos_lt; lia.
  - apply zb2_ga_pos_neq0. apply QltT_to_Qlt. apply zb2_ga_natpos_lt. lia.
  - apply zb2_ga_pos_neq0. apply Qmult_lt_0_compat; apply QltT_to_Qlt;
      apply zb2_ga_natpos_lt; lia.
Qed.

(* ===================================================================== *)
(* §2 Hpw 峰核机制形（供件位二·加权比率律 + 升降档单调律 + 峰带归约）       *)
(* ===================================================================== *)

(* 逐点封顶量：Wt n j = term(n,j)·(j+1)·(j+2)（a1 Hpw 前提左端逐字形）。 *)
Definition zb2_sup_Wt (n j : nat) : Q :=
  zb2_term n j * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1).

(* 加权比率恒等式：Wt(n,j+1)·(j+1)²·(2n+j+2)² == Wt(n,j)·(n+j+1)³·(j+3)。
   铸法：gapA 无权比率律（term(n,j+1)·(j+1)·(2n+j+2)² == term(n,j)·(n+j+1)³）
   两侧按 (j+2)(j+3)(j+1)(2n+j+2)² 加权重排（ring），代入比率律后 ring 合账。 *)
Lemma zb2_sup_Hpw_ratio : forall n j : nat,
  QeqT (zb2_sup_Wt n (Datatypes.S j)
        * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
           * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))
       (zb2_sup_Wt n j
        * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
           * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))).
Proof.
  intros n j.
  pose proof (qeqT_imp_qeq _ _ (zb2_ga_term_ratio n j)) as Hr.
  replace (n + Datatypes.S j + n + 1)%nat with (2 * n + j + 2)%nat in Hr by lia.
  replace (n + Datatypes.S j)%nat with (n + j + 1)%nat in Hr by lia.
  unfold zb2_sup_Wt.
  replace (Datatypes.S j + 2)%nat with (j + 3)%nat by lia.
  replace (Datatypes.S (Datatypes.S j))%nat with (j + 2)%nat by lia.
  apply qeq_imp_qeqT.
  assert (E1 : (zb2_term n (Datatypes.S j)
                * (Z.of_nat (j + 2) # 1) * (Z.of_nat (j + 3) # 1))
               * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
                  * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
            == (zb2_term n (Datatypes.S j)
                * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))
               * ((Z.of_nat (j + 2) # 1) * (Z.of_nat (j + 3) # 1)
                  * (Z.of_nat (Datatypes.S j) # 1)))
    by ring.
  rewrite E1, Hr. ring.
Qed.

(* Wt 非负面（供升降档乘法合账）。 *)
Lemma zb2_sup_Wt_ge0 : forall n j : nat, 0 <= zb2_sup_Wt n j.
Proof.
  intros n j. unfold zb2_sup_Wt. apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply (Qlt_le_weak 0). apply QltT_to_Qlt. apply zb2_term_pos.
    + apply zb2_ia_natpos_ge.
  - apply zb2_ia_natpos_ge.
Qed.

(* 四因子严格正：0 < p1、0 < p2、0 < p3、0 < p4 则 0 < ((p1·p2)·p3)·p4。 *)
Lemma zb2_sup_P4_lt : forall p1 p2 p3 p4 : Q,
  0 < p1 -> 0 < p2 -> 0 < p3 -> 0 < p4 -> 0 < (((p1 * p2) * p3) * p4)%Q.
Proof.
  intros p1 p2 p3 p4 H1 H2 H3 H4. apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat.
      * exact H1.
      * exact H2.
    + exact H3.
  - exact H4.
Qed.

(* 升档单调律：2(j+2) ≤ n 时 Wt(n,j) ≤ Wt(n,j+1)。
   差额四次型 (j+1)²(2n+j+2)² ≤ (n+j+1)³(j+3) 于代换 n = 2(j+2)+u 后
   全系数为正（zia 展开 2t⁴+58t³+… ≥ 0），nia 一发。 *)
Theorem zb2_sup_Hpw_rise : forall n j : nat, (2 * (j + 2) <= n)%nat ->
  QleT' (zb2_sup_Wt n j) (zb2_sup_Wt n (Datatypes.S j)).
Proof.
  intros n j H. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (zb2_sup_Hpw_ratio n j)) as Hr.
  assert (HPQ : ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
                 * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
             <= ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                 * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))).
  { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    assert (Hz : (Z.of_nat (Datatypes.S j) * Z.of_nat (Datatypes.S j)
                  * (Z.of_nat (2 * n + j + 2) * Z.of_nat (2 * n + j + 2))
              <= Z.of_nat (n + j + 1) * Z.of_nat (n + j + 1)
                 * Z.of_nat (n + j + 1) * Z.of_nat (j + 3))%Z).
    { remember (n - 2 * (j + 2))%nat as u eqn:Eu.
      assert (Hu : (n = 2 * (j + 2) + u)%nat) by lia.
      rewrite Hu. nia. }
    nia. }
  pose proof (zb2_sup_Wt_ge0 n j) as HW0.
  apply (zb2_ia_cancel_r (zb2_sup_Wt n j) (zb2_sup_Wt n (Datatypes.S j))
           ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
            * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))).
  - apply zb2_sup_P4_lt; apply zb2_ia_natpos_lt; lia.
  - apply (Qle_trans (zb2_sup_Wt n j * ((Z.of_nat (Datatypes.S j) # 1)
             * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)
             * (Z.of_nat (2 * n + j + 2) # 1)))
            (zb2_sup_Wt n j * ((Z.of_nat (n + j + 1) # 1)
             * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
             * (Z.of_nat (j + 3) # 1)))
            (zb2_sup_Wt n (Datatypes.S j) * ((Z.of_nat (Datatypes.S j) # 1)
             * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)
             * (Z.of_nat (2 * n + j + 2) # 1)))).
    + assert (HE1 : zb2_sup_Wt n j * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1))
                == ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
                    * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
                   * zb2_sup_Wt n j) by ring.
      assert (HE2 : zb2_sup_Wt n j * ((Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (j + 3) # 1))
                == ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                    * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                   * zb2_sup_Wt n j) by ring.
      rewrite HE1, HE2. apply (Qmult_le_compat_r _ _ _ HPQ HW0).
    + rewrite Hr. apply Qle_refl.
Qed.

(* j = 0 档升档律：1 ≤ n 时 Wt(n,0) ≤ Wt(n,1)（比率律 j=0 实例 +
   四次型 (2n+2)² ≤ (n+1)³·3，代换 n = 1+u 后 nia）。 *)
Lemma zb2_sup_rise_s0 : forall n : nat, (1 <= n)%nat ->
  QleT' (zb2_sup_Wt n 0) (zb2_sup_Wt n 1).
Proof.
  intros n Hn. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (zb2_sup_Hpw_ratio n 0)) as Hr.
  replace (2 * n + 0 + 2)%nat with (2 * n + 2)%nat in Hr by lia.
  replace (n + 0 + 1)%nat with (n + 1)%nat in Hr by lia.
  replace (0 + 3)%nat with 3%nat in Hr by lia.
  apply (zb2_ia_cancel_r (zb2_sup_Wt n 0) (zb2_sup_Wt n 1)
           ((Z.of_nat 1 # 1) * (Z.of_nat 1 # 1)
            * (Z.of_nat (2 * n + 2) # 1) * (Z.of_nat (2 * n + 2) # 1))).
  - apply zb2_sup_P4_lt; apply zb2_ia_natpos_lt; lia.
  - pose proof (zb2_sup_Wt_ge0 n 0) as HW0.
    apply (Qle_trans (zb2_sup_Wt n 0 * ((Z.of_nat 1 # 1) * (Z.of_nat 1 # 1)
             * (Z.of_nat (2 * n + 2) # 1) * (Z.of_nat (2 * n + 2) # 1)))
            (zb2_sup_Wt n 0 * ((Z.of_nat (n + 1) # 1) * (Z.of_nat (n + 1) # 1)
             * (Z.of_nat (n + 1) # 1) * (Z.of_nat 3 # 1)))
            (zb2_sup_Wt n 1 * ((Z.of_nat 1 # 1) * (Z.of_nat 1 # 1)
             * (Z.of_nat (2 * n + 2) # 1) * (Z.of_nat (2 * n + 2) # 1)))).
    + assert (HE1 : zb2_sup_Wt n 0 * ((Z.of_nat 1 # 1) * (Z.of_nat 1 # 1)
                   * (Z.of_nat (2 * n + 2) # 1) * (Z.of_nat (2 * n + 2) # 1))
                == ((Z.of_nat 1 # 1) * (Z.of_nat 1 # 1)
                    * (Z.of_nat (2 * n + 2) # 1) * (Z.of_nat (2 * n + 2) # 1))
                   * zb2_sup_Wt n 0) by ring.
      assert (HE2 : zb2_sup_Wt n 0 * ((Z.of_nat (n + 1) # 1) * (Z.of_nat (n + 1) # 1)
                   * (Z.of_nat (n + 1) # 1) * (Z.of_nat 3 # 1))
                == ((Z.of_nat (n + 1) # 1) * (Z.of_nat (n + 1) # 1)
                    * (Z.of_nat (n + 1) # 1) * (Z.of_nat 3 # 1))
                   * zb2_sup_Wt n 0) by ring.
      assert (HPQ : ((Z.of_nat 1 # 1) * (Z.of_nat 1 # 1)
                     * (Z.of_nat (2 * n + 2) # 1) * (Z.of_nat (2 * n + 2) # 1))
                 <= ((Z.of_nat (n + 1) # 1) * (Z.of_nat (n + 1) # 1)
                     * (Z.of_nat (n + 1) # 1) * (Z.of_nat 3 # 1))).
      { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
        assert (Hz : (Z.of_nat 1 * Z.of_nat 1 * (Z.of_nat (2 * n + 2) * Z.of_nat (2 * n + 2))
                  <= Z.of_nat (n + 1) * Z.of_nat (n + 1) * Z.of_nat (n + 1)
                     * Z.of_nat 3)%Z).
        { remember (n - 1)%nat as u eqn:Eu.
          assert (Hu : (n = 1 + u)%nat) by lia.
          rewrite Hu. nia. }
        nia. }
      rewrite HE1, HE2. apply (Qmult_le_compat_r _ _ _ HPQ HW0).
    + rewrite Hr. apply Qle_refl.
Qed.

(* j = 1 档升档律：1 ≤ n 时 Wt(n,1) ≤ Wt(n,2)（比率律 j=1 实例 +
   四次型 4·(2n+3)² ≤ (n+2)³·4，代换 n = 1+u 后 nia）。 *)
Lemma zb2_sup_rise_s1 : forall n : nat, (1 <= n)%nat ->
  QleT' (zb2_sup_Wt n 1) (zb2_sup_Wt n 2).
Proof.
  intros n Hn. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (zb2_sup_Hpw_ratio n 1)) as Hr.
  replace (2 * n + 1 + 2)%nat with (2 * n + 3)%nat in Hr by lia.
  replace (n + 1 + 1)%nat with (n + 2)%nat in Hr by lia.
  replace (1 + 3)%nat with 4%nat in Hr by lia.
  replace (Datatypes.S 1)%nat with 2%nat in Hr by lia.
  apply (zb2_ia_cancel_r (zb2_sup_Wt n 1) (zb2_sup_Wt n 2)
           ((Z.of_nat 2 # 1) * (Z.of_nat 2 # 1)
            * (Z.of_nat (2 * n + 3) # 1) * (Z.of_nat (2 * n + 3) # 1))).
  - apply zb2_sup_P4_lt; apply zb2_ia_natpos_lt; lia.
  - pose proof (zb2_sup_Wt_ge0 n 1) as HW0.
    apply (Qle_trans (zb2_sup_Wt n 1 * ((Z.of_nat 2 # 1) * (Z.of_nat 2 # 1)
             * (Z.of_nat (2 * n + 3) # 1) * (Z.of_nat (2 * n + 3) # 1)))
            (zb2_sup_Wt n 1 * ((Z.of_nat (n + 2) # 1) * (Z.of_nat (n + 2) # 1)
             * (Z.of_nat (n + 2) # 1) * (Z.of_nat 4 # 1)))
            (zb2_sup_Wt n 2 * ((Z.of_nat 2 # 1) * (Z.of_nat 2 # 1)
             * (Z.of_nat (2 * n + 3) # 1) * (Z.of_nat (2 * n + 3) # 1)))).
    + assert (HE1 : zb2_sup_Wt n 1 * ((Z.of_nat 2 # 1) * (Z.of_nat 2 # 1)
                   * (Z.of_nat (2 * n + 3) # 1) * (Z.of_nat (2 * n + 3) # 1))
                == ((Z.of_nat 2 # 1) * (Z.of_nat 2 # 1)
                    * (Z.of_nat (2 * n + 3) # 1) * (Z.of_nat (2 * n + 3) # 1))
                   * zb2_sup_Wt n 1) by ring.
      assert (HE2 : zb2_sup_Wt n 1 * ((Z.of_nat (n + 2) # 1) * (Z.of_nat (n + 2) # 1)
                   * (Z.of_nat (n + 2) # 1) * (Z.of_nat 4 # 1))
                == ((Z.of_nat (n + 2) # 1) * (Z.of_nat (n + 2) # 1)
                    * (Z.of_nat (n + 2) # 1) * (Z.of_nat 4 # 1))
                   * zb2_sup_Wt n 1) by ring.
      assert (HPQ : ((Z.of_nat 2 # 1) * (Z.of_nat 2 # 1)
                     * (Z.of_nat (2 * n + 3) # 1) * (Z.of_nat (2 * n + 3) # 1))
                 <= ((Z.of_nat (n + 2) # 1) * (Z.of_nat (n + 2) # 1)
                     * (Z.of_nat (n + 2) # 1) * (Z.of_nat 4 # 1))).
      { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
        assert (Hz : (Z.of_nat 2 * Z.of_nat 2
                      * (Z.of_nat (2 * n + 3) * Z.of_nat (2 * n + 3))
                  <= Z.of_nat (n + 2) * Z.of_nat (n + 2) * Z.of_nat (n + 2)
                     * Z.of_nat 4)%Z).
        { remember (n - 1)%nat as u eqn:Eu.
          assert (Hu : (n = 1 + u)%nat) by lia.
          rewrite Hu. nia. }
        nia. }
      rewrite HE1, HE2. apply (Qmult_le_compat_r _ _ _ HPQ HW0).
    + rewrite Hr. apply Qle_refl.
Qed.

(* 升档步律合成：1 ≤ n 且 2k+4 ≤ n 时 Wt(n,k) ≤ Wt(n,k+1)。
   k ≤ 1 档走 s0/s1，k ≥ 2 档走升档单调律（2k+4 ≤ n 即 2(k+2) ≤ n）。 *)
Lemma zb2_sup_rise_step : forall n k : nat, (1 <= n)%nat -> (2 * k + 4 <= n)%nat ->
  Qle (zb2_sup_Wt n k) (zb2_sup_Wt n (Datatypes.S k)).
Proof.
  intros n k Hn Hk. destruct k as [| [| k']].
  - apply QleT'_to_Qle. apply zb2_sup_rise_s0. exact Hn.
  - apply QleT'_to_Qle. apply zb2_sup_rise_s1. exact Hn.
  - apply QleT'_to_Qle. apply zb2_sup_Hpw_rise. lia.
Qed.

(* 升档链机：a ≤ b 且 2b+4 ≤ n 时 Wt(n,a) ≤ Wt(n,b+1)（逐档爬升）。 *)
Lemma zb2_sup_rise_chain : forall n a b : nat, (1 <= n)%nat -> (a <= b)%nat ->
  (2 * b + 4 <= n)%nat -> Qle (zb2_sup_Wt n a) (zb2_sup_Wt n (Datatypes.S b)).
Proof.
  intros n a b Hn Hab Hk. induction b as [| b IH].
  - assert (Ha : (a = 0)%nat) by lia. subst a.
    apply zb2_sup_rise_step; lia.
  - destruct (Nat.eq_dec a (Datatypes.S b)) as [Heq | Hne].
    + subst a. apply zb2_sup_rise_step; lia.
    + assert (Hale : (a <= b)%nat) by lia.
      assert (Hkb : (2 * b + 4 <= n)%nat) by lia.
      pose proof (IH Hale Hkb) as IHq.
      pose proof (zb2_sup_rise_step n (Datatypes.S b) Hn Hk) as Hstep.
      apply (Qle_trans _ (zb2_sup_Wt n (Datatypes.S b))); assumption.
Qed.

(* 降档单调律：9 ≤ n 且 n ≤ j 时 Wt(n,j+1) ≤ Wt(n,j)。
   差额四次型 (n+j+1)³(j+3) ≤ (j+1)²(2n+j+2)² 于代换 n = 9+v、j = 9+v+d
   后全系数为负（−v⁴−30v³d−… ≤ 0），nia 一发。 *)
Theorem zb2_sup_Hpw_fall : forall n j : nat, (9 <= n)%nat -> (n <= j)%nat ->
  QleT' (zb2_sup_Wt n (Datatypes.S j)) (zb2_sup_Wt n j).
Proof.
  intros n j Hn Hj. apply Qle_to_QleT'.
  pose proof (qeqT_imp_qeq _ _ (zb2_sup_Hpw_ratio n j)) as Hr.
  assert (HQP : ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                 * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
             <= ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
                 * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))).
  { unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    assert (Hz : (Z.of_nat (n + j + 1) * Z.of_nat (n + j + 1)
                  * Z.of_nat (n + j + 1) * Z.of_nat (j + 3)
              <= Z.of_nat (Datatypes.S j) * Z.of_nat (Datatypes.S j)
                 * (Z.of_nat (2 * n + j + 2) * Z.of_nat (2 * n + j + 2)))%Z).
    { remember (n - 9)%nat as v eqn:Ev.
      assert (Hv2 : (n = 9 + v)%nat) by lia.
      rewrite Hv2.
      remember (j - (9 + v))%nat as d eqn:Ed.
      assert (Hd2 : (j = 9 + v + d)%nat) by lia.
      rewrite Hd2. nia. }
    nia. }
  pose proof (zb2_sup_Wt_ge0 n j) as HW0.
  apply (zb2_ia_cancel_r (zb2_sup_Wt n (Datatypes.S j)) (zb2_sup_Wt n j)
           ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
            * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))).
  - apply zb2_sup_P4_lt; apply zb2_ia_natpos_lt; lia.
  - apply (Qle_trans (zb2_sup_Wt n (Datatypes.S j) * ((Z.of_nat (Datatypes.S j) # 1)
             * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)
             * (Z.of_nat (2 * n + j + 2) # 1)))
            (zb2_sup_Wt n j * ((Z.of_nat (n + j + 1) # 1)
             * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
             * (Z.of_nat (j + 3) # 1)))
            (zb2_sup_Wt n j * ((Z.of_nat (Datatypes.S j) # 1)
             * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)
             * (Z.of_nat (2 * n + j + 2) # 1)))).
    + rewrite Hr. apply Qle_refl.
    + assert (HE3 : zb2_sup_Wt n j * ((Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (j + 3) # 1))
                == ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                    * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                   * zb2_sup_Wt n j) by ring.
      assert (HE4 : zb2_sup_Wt n j * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1))
                == ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (Datatypes.S j) # 1)
                    * (Z.of_nat (2 * n + j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
                   * zb2_sup_Wt n j) by ring.
      rewrite HE3, HE4. apply (Qmult_le_compat_r _ _ _ HQP HW0).
Qed.

(* 降档链机：9 ≤ n 时 Wt(n, n+d) ≤ Wt(n,n)（自任意 j ≥ n 逐档降至 n）。 *)
Lemma zb2_sup_fall_chain : forall n d : nat, (9 <= n)%nat ->
  Qle (zb2_sup_Wt n (n + d)) (zb2_sup_Wt n n).
Proof.
  intros n d Hn. induction d as [| d IH].
  - rewrite Nat.add_0_r. apply Qle_refl.
  - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
    apply (Qle_trans _ (zb2_sup_Wt n (n + d))).
    + apply QleT'_to_Qle. apply zb2_sup_Hpw_fall; lia.
    + exact IH.
Qed.

(* 峰带归约定理（Hpw 机证形·诚实接口）：
   对 8 ≤ m，只要峰带 [k0, m+1]（2·k0+2 ≤ m+1）内逐点封顶证书在句，
   即得全窗 ∀j 的逐点封顶 Wt(m+1,j) ≤ (1/10)·(1/10)^m。
   铸法：j < k0 走升档链至 k0（2·k0+2 ≤ m+1 即链条件 2·k0'+4 ≤ m+1），
   k0 ≤ j ≤ m+1 直取带内证书，j > m+1 走降档链至 m+1。
   峰带逐点证书即 Hpw 残余缺口之精确刻形（k0 ≤ (m-1)/2，带长约 n/2）。 *)
Theorem zb2_sup_Hpw_reduce : forall m k0 : nat, (8 <= m)%nat ->
  (2 * k0 + 2 <= Datatypes.S m)%nat ->
  (forall k : nat, (k0 <= k <= Datatypes.S m)%nat ->
     QleT' (zb2_sup_Wt (Datatypes.S m) k) ((1 # 10) * q_pow (1 # 10) m)) ->
  forall j : nat,
     QleT' (zb2_sup_Wt (Datatypes.S m) j) ((1 # 10) * q_pow (1 # 10) m).
Proof.
  intros m k0 Hm Hk0 Hband j.
  destruct (le_lt_dec j (Datatypes.S m)) as [Hj1 | Hj2].
  - destruct (le_lt_dec k0 j) as [Hin | Hlo].
    + apply Hband. lia.
    + destruct k0 as [| k0'].
      * exfalso. lia.
      * apply Qle_to_QleT'.
        assert (Hchain : Qle (zb2_sup_Wt (Datatypes.S m) j)
                             (zb2_sup_Wt (Datatypes.S m) (Datatypes.S k0'))).
        { apply (zb2_sup_rise_chain (Datatypes.S m) j k0').
          - lia.
          - lia.
          - lia. }
        apply (Qle_trans _ (zb2_sup_Wt (Datatypes.S m) (Datatypes.S k0'))).
        -- exact Hchain.
        -- apply QleT'_to_Qle. apply Hband. lia.
  - apply Qle_to_QleT'.
    assert (Hd : j = (Datatypes.S m + (j - Datatypes.S m))%nat) by lia.
    pose proof (zb2_sup_fall_chain (Datatypes.S m) (j - Datatypes.S m) ltac:(lia))
      as Hfc.
    rewrite <- Hd in Hfc.
    apply (Qle_trans _ (zb2_sup_Wt (Datatypes.S m) (Datatypes.S m))).
    + exact Hfc.
    + apply QleT'_to_Qle. apply Hband. lia.
Qed.

(* ===================================================================== *)
(* §3 尾舱：语句公理面自检                                                *)
(* ===================================================================== *)

Print Assumptions zb2_sup_qeq_cancel_r.
Print Assumptions zb2_sup_qstep.
Print Assumptions zb2_sup_qshift.
Print Assumptions zb2_sup_Ws_step.
Print Assumptions zb2_sup_Wt_ge0.
Print Assumptions zb2_sup_Hpw_ratio.
Print Assumptions zb2_sup_Hpw_rise.
Print Assumptions zb2_sup_rise_s0.
Print Assumptions zb2_sup_rise_s1.
Print Assumptions zb2_sup_rise_step.
Print Assumptions zb2_sup_rise_chain.
Print Assumptions zb2_sup_Hpw_fall.
Print Assumptions zb2_sup_fall_chain.
Print Assumptions zb2_sup_Hpw_reduce.
