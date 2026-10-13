(* ===================================================================== *)
(* 模块：u5c_zeta2_gapA                                                  *)
(* 使命：ζ(2) 可及档切片施工图缺口件 A——decay 件 zb2_dc_sep_small 显式     *)
(*   前提 II（逐点到积分肢：zb2_Isum (S m) M ≤ (1/4)(1/10)^m）验收位的     *)
(*   A2 级数比率绕开路线供给机。本件铸出并全证（零承认）：                *)
(*   ① 二项式乘法步进（Pascal 双生恒等式 H/G 联合归纳）；                 *)
(*   ② zb2_term 逐档精确比率律（交叉相乘 QeqT Set 承载形）；               *)
(*   ③ 两因子不等式：A 因子 (n+j+1)(j+3) ≤ (j+2)(2n+j+2)（无条件）；       *)
(*      B 因子 (n+j+1)² ≤ (j+1)(2n+j+2)（阈值 n² ≤ j+1）；                *)
(*   ④ 阈值形逐档下降与单调：term(n,S j)·(j+3) ≤ term(n,j)·(j+2) 且       *)
(*      term(n,S j) ≤ term(n,j)；                                         *)
(*   ⑤ 尾界机（S-2 验收「尾界 ≤ 显式 Q 式」的 θ=1 收窄形）：               *)
(*      zb2_Isum n M ≤ zb2_Isum n J + (M−J)·term(n,J)（J ≤ M、阈值内）；   *)
(*      及 sep_small 前提 II 对接形实例（n = S m、J = m²+2m）。            *)
(* 【响亮登记·收窄申报（诚实律）】终闭口语句 ∀ m M, zb2_Isum (S m) M ≤     *)
(*   (1/4)(1/10)^m 本件未铸——施工实测三事实：                             *)
(*   (a) term 比率非单调：r_j = (n+j+1)³/((j+1)(2n+j+2)²) 随 j 先升后降    *)
(*       再趋 1（j→∞ 时 r_j → 1），故 θ<1 几何尾界机在本级数上数学不可能； *)
(*   (b) 多项式尾证书 r_j ≤ ((j+2)/(j+3))² 仅在 j ≳ 2n−1 窗内成立         *)
(*       （n=9 实测 j=8 差 1e-4 失配、j=9 起成立）；                        *)
(*   (c) 逐点 (j+1)(j+2) 证书的符号 n 峰分析余量仅 ~3.3 倍                *)
(*       （n=9 峰 j≈6：7.48e-11 vs 2.5e-10），非单一工作窗可尽。                *)
(*   故终闭口须「初始段 Isum(S m, m²+2m) 符号界＋收敛尾界机」两件后续，    *)
(*   勘形单 §3 S-2「单一工作窗 300–500 行」估额按实况上调并附复审触发。          *)
(* 依赖：Stdlib（QArith/ZArith/Arith/Lia）；缓存根 S01_BaseRing、          *)
(*   S02_CauchyComplete、S03_QExp、BeukersLists；tmine04 池                *)
(*   abl_z2_itg_carrier（zb2_term/zb2_Isum/zb2_term_pos）。                *)
(*   零外部证书器、零实数层、零经典逻辑。                                  *)
(* 构造性：纯构造性、零假设声明、零承认式语句；语句面全 Set 层               *)
(*   （QleT'/QltT/QeqT），归纳与情形分析均经可判定通路（Nat.eq_dec），零公理。*)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*   ulimit -s 65532 && cd 沙箱/现役/abl_zeta2_pool &&                    *)
(*   rocq c -native-compiler no -q -Q . ""                                *)
(*   -Q <绝对路径>/abl_tmine04_pool/zeta2 ""                              *)
(*   -Q <绝对路径>/vo_local_world_unified_0930 "" u5c_zeta2_gapA.v        *)
(*   （三根 -Q 配平：本池/tmine04 池/缓存根）。                           *)
(* 对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.     *)
(*   London Math. Soc. 11 (1979) 级数比率估计；勘形单 _tdm225Z2 §3 S-2。   *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_itg_carrier.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 基础档：Set 层序转换、取消律、正数值面                              *)
(* ===================================================================== *)

(* 正数值面：k ≥ 1 ⟹ 0 < (k)#1（供取消律；QltT Set 承载） *)
Lemma zb2_ga_natpos_lt : forall k : nat, (1 <= k)%nat -> QltT 0 (Z.of_nat k # 1).
Proof.
  intro k. destruct k as [| k']; intro Hk.
  - exfalso. lia.
  - apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* 非负数值面：0 ≤ (k)#1（任意 nat；QleT' Set 承载） *)
Lemma zb2_ga_natpos_ge : forall k : nat, QleT' 0 (Z.of_nat k # 1).
Proof.
  intro k. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(* 正因子取消律：0 < c 且 a·c ≤ b·c ⟹ a ≤ b（反证：b < a 时正因子保严格序） *)
Lemma zb2_ga_cancel_r : forall a b c : Q, 0 < c -> a * c <= b * c -> a <= b.
Proof.
  intros a b c Hc H.
  destruct (Qlt_le_dec b a) as [Hlt | Hle].
  - exfalso.
    assert (Hlt2 : b * c < a * c) by (apply (Qmult_lt_compat_r b a c Hc Hlt)).
    exact (Qlt_not_le (b * c) (a * c) Hlt2 H).
  - exact Hle.
Qed.

(* 非负乘积序传递：0 ≤ a、0 ≤ c、a ≤ b、c ≤ d ⟹ a·c ≤ b·d *)
Lemma zb2_ga_mult_le : forall a b c d : Q,
  0 <= a -> 0 <= c -> a <= b -> c <= d -> a * c <= b * d.
Proof.
  intros a b c d Ha Hc Hab Hcd.
  apply (Qle_trans (a * c) (b * c) (b * d)).
  - exact (Qmult_le_compat_r a b c Hab Hc).
  - assert (Hb0 : 0 <= b) by (apply (Qle_trans 0 a b); [ exact Ha | exact Hab ]).
    assert (HE1 : b * c == c * b) by ring.
    assert (HE2 : b * d == d * b) by ring.
    rewrite HE1. rewrite HE2.
    exact (Qmult_le_compat_r c d b Hcd Hb0).
Qed.

(* ===================================================================== *)
(* §1 二项式乘法步进（Pascal 双生恒等式联合归纳）                          *)
(* ===================================================================== *)

(* 边缘值：C(m+1, m) = m+1（对 m 归纳，Pascal 展开） *)
Lemma zb2_ga_bkC_edge : forall m : nat, bkC (Datatypes.S m) m = Datatypes.S m.
Proof.
  induction m as [| m IH].
  - cbn [bkC]. lia.
  - assert (HP : (bkC (Datatypes.S (Datatypes.S m)) (Datatypes.S m)
               = bkC (Datatypes.S m) m + bkC (Datatypes.S m) (Datatypes.S m))%nat)
      by (exact (bkC_pascal_shift (Datatypes.S m) (Datatypes.S m))).
    rewrite HP. rewrite bkC_diag. rewrite IH. lia.
Qed.

(* 双生恒等式（对 k 联合归纳；bkC = Pascal 二项式系数）：
   H(k,r)：C(k+1,r)·(k+1−r) = C(k,r)·(k+1)；
   G(k,r)：C(k+1,r+1)·(r+1) = C(k,r)·(k+1)。
   步档各以 Pascal 展开 C(k+2,·) 后互喂对方在 k 档的实例；
   差值 (k−j) 经 remember 隔离为原子 p，步档化为纯乘加恒等式。 *)
Lemma zb2_ga_bkC_HG : forall k : nat,
  (forall r : nat, (r <= k)%nat ->
     (bkC (Datatypes.S k) r * (Datatypes.S k - r) = bkC k r * Datatypes.S k)%nat)
  /\ (forall r : nat, (r <= k)%nat ->
     (bkC (Datatypes.S k) (Datatypes.S r) * Datatypes.S r
      = bkC k r * Datatypes.S k)%nat).
Proof.
  induction k as [| k IH].
  - split.
    + intros r Hr. assert (Hr0 : (r = 0)%nat) by lia. subst r.
      cbn [bkC]. lia.
    + intros r Hr. assert (Hr0 : (r = 0)%nat) by lia. subst r.
      cbn [bkC]. lia.
  - destruct IH as [IHh IHg]. split.
    + (* H(S k, r) *)
      intros r Hr. destruct r as [| j].
      * cbn [bkC]. lia.
      * assert (Hjk : (j <= k)%nat) by lia.
        specialize (IHh j Hjk). specialize (IHg j Hjk).
        assert (HP : (bkC (Datatypes.S (Datatypes.S k)) (Datatypes.S j)
                   = bkC (Datatypes.S k) j + bkC (Datatypes.S k) (Datatypes.S j))%nat)
          by (exact (bkC_pascal_shift (Datatypes.S k) (Datatypes.S j))).
        rewrite HP.
        assert (Hsub : (Datatypes.S (Datatypes.S k) - Datatypes.S j
                      = Datatypes.S k - j)%nat) by lia.
        rewrite Hsub.
        assert (Hsp : (Datatypes.S (Datatypes.S k)
                     = Datatypes.S j + (Datatypes.S k - j))%nat) by lia.
        remember (Datatypes.S k - j)%nat as p eqn:Hpdef in *.
        rewrite Hsp, Nat.mul_add_distr_l, Nat.mul_add_distr_r, IHh, IHg. lia.
    + (* G(S k, r) *)
      intros r Hr. destruct (Nat.eq_dec r (Datatypes.S k)) as [Heq | Hne].
      * subst r. rewrite bkC_diag. rewrite bkC_diag. lia.
      * assert (Hrk : (r <= k)%nat) by lia.
        specialize (IHh r Hrk). specialize (IHg r Hrk).
        assert (HP : (bkC (Datatypes.S (Datatypes.S k)) (Datatypes.S r)
                   = bkC (Datatypes.S k) r + bkC (Datatypes.S k) (Datatypes.S r))%nat)
          by (exact (bkC_pascal_shift (Datatypes.S k) (Datatypes.S r))).
        rewrite HP.
        assert (Hsp : (Datatypes.S (Datatypes.S k)
                     = Datatypes.S r + (Datatypes.S k - r))%nat) by lia.
        remember (Datatypes.S k - r)%nat as p eqn:Hpdef in *.
        rewrite Hsp, Nat.mul_add_distr_l, Nat.mul_add_distr_r, IHh, IHg. lia.
Qed.

(* 乘法步进主句：C(n+j+1, n)·(j+1) = C(n+j, n)·(n+j+1)
   （k := n+j、r := n 的 H 实例；j+1 = k+1−n、n+j+1 = k+1） *)
Lemma zb2_ga_bkC_step : forall n j : nat,
  (bkC (n + Datatypes.S j) n * Datatypes.S j
  = bkC (n + j) n * (n + Datatypes.S j))%nat.
Proof.
  intros n j.
  destruct (zb2_ga_bkC_HG (n + j)) as [IHh _].
  assert (Hle : (n <= n + j)%nat) by lia.
  pose proof (IHh n Hle) as HH.
  replace (Datatypes.S (n + j) - n)%nat with (Datatypes.S j) in HH by lia.
  replace (Datatypes.S (n + j))%nat with (n + Datatypes.S j)%nat in HH by lia.
  exact HH.
Qed.

(* ===================================================================== *)
(* §2 zb2_term 精确比率律（交叉相乘 Qeq 形）                               *)
(* ===================================================================== *)

(* 正有理数非零：0 < x 则 x ≠ 0（分式归一等式的侧条件消解用） *)
Lemma zb2_ga_pos_neq0 : forall x : Q, 0 < x -> ~ (x == 0).
Proof.
  intros x Hx. exact (Qnot_eq_sym 0 x (Qlt_not_eq 0 x Hx)).
Qed.

(* 侧条件消解：field 侧条件为「各分母原子非零」的合取；
   每一支为 q_fact 原子或 (S k)#1 原子（或其正乘积），皆正故非零 *)
Ltac zb2_ga_nonzero :=
  repeat split;
  first [ apply zb2_ga_pos_neq0; apply q_fact_pos
        | apply zb2_ga_pos_neq0; apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia
        | apply zb2_ga_pos_neq0; apply Qmult_lt_0_compat;
            [ apply q_fact_pos | apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia ]
        | apply zb2_ga_pos_neq0; apply Qmult_lt_0_compat;
            [ apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia | apply q_fact_pos ]
        | apply zb2_ga_pos_neq0; apply Qmult_lt_0_compat;
            [ apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia
            | apply QltT_to_Qlt; apply zb2_ga_natpos_lt; lia ] ].

(* 比率律：term(n, j+1)·(j+1)·(2n+j+2)² = term(n, j)·(n+j+1)³。
   即 r_j = term(n,j+1)/term(n,j) = (n+j+1)³/((j+1)(2n+j+2)²) 的无除法形。
   铸法：q_fact 后继展开（n+S j = S(n+j)、n+S j+n+1 = S(n+j+n+1)）后
   两侧各自归拢到公共形 (bkC…)·(步进因子)·B(n+j,n)²，再代入 bkC 步进。 *)
Lemma zb2_ga_term_ratio : forall n j : nat,
  QeqT (zb2_term n (Datatypes.S j)
        * ((Z.of_nat (Datatypes.S j) # 1)
           * (Z.of_nat (n + Datatypes.S j + n + 1) # 1)
           * (Z.of_nat (n + Datatypes.S j + n + 1) # 1)))
       (zb2_term n j
        * ((Z.of_nat (n + Datatypes.S j) # 1)
           * (Z.of_nat (n + Datatypes.S j) # 1)
           * (Z.of_nat (n + Datatypes.S j) # 1))).
Proof.
  intros n j. apply qeq_imp_qeqT. unfold zb2_term.
  replace (n + Datatypes.S j + n + 1)%nat with (Datatypes.S (n + j + n + 1)) by lia.
  replace (n + Datatypes.S j)%nat with (Datatypes.S (n + j)) by lia.
  rewrite (q_fact_succ (n + j)). rewrite (q_fact_succ (n + j + n + 1)).
  pose proof (zb2_ga_bkC_step n j) as Hs.
  replace (n + Datatypes.S j)%nat with (Datatypes.S (n + j)) in Hs by lia.
  assert (HbkQ : (Z.of_nat (bkC (Datatypes.S (n + j)) n) # 1)
                 * (Z.of_nat (Datatypes.S j) # 1)
              == (Z.of_nat (bkC (n + j) n) # 1)
                 * (Z.of_nat (Datatypes.S (n + j)) # 1)).
  { assert (Hz : (Z.of_nat (bkC (Datatypes.S (n + j)) n) * Z.of_nat (Datatypes.S j)
               = Z.of_nat (bkC (n + j) n) * Z.of_nat (Datatypes.S (n + j)))%Z).
    { rewrite <- !Nat2Z.inj_mul. f_equal. exact Hs. }
    unfold Qeq. cbn [Qnum Qden Qmult]. rewrite Hz. lia. }
  transitivity ((Z.of_nat (bkC (Datatypes.S (n + j)) n) # 1)
                * (Z.of_nat (Datatypes.S j) # 1)
                * ((Z.of_nat (Datatypes.S (n + j)) # 1)
                   * (Z.of_nat (Datatypes.S (n + j)) # 1))
                * (q_fact (n + j) * q_fact n / q_fact (n + j + n + 1))
                * (q_fact (n + j) * q_fact n / q_fact (n + j + n + 1))).
  { field; zb2_ga_nonzero. }
  rewrite HbkQ.
  field; zb2_ga_nonzero.
Qed.

(* ===================================================================== *)
(* §3 两因子不等式（A 因子无条件；B 因子阈值形）                           *)
(* ===================================================================== *)

(* A 因子（无条件）：(n+j+1)(j+3) ≤ (j+2)(2n+j+2)。
   差 = n·j + n + 1 ≥ 1 恒正，全龄段成立。 *)
Lemma zb2_ga_A_le : forall n j : nat,
  QleT' ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
        ((Z.of_nat (j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1)).
Proof.
  intros n j. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. nia.
Qed.

(* B 因子（阈值形）：n² ≤ j+1 ⟹ (n+j+1)² ≤ (j+1)(2n+j+2)。
   差 = j+1−n² ≥ 0。 *)
Lemma zb2_ga_B_le : forall n j : nat, (n * n <= Datatypes.S j)%nat ->
  QleT' ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))
        ((Z.of_nat (j + 1) # 1) * (Z.of_nat (2 * n + j + 2) # 1)).
Proof.
  intros n j Hsq. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul]. nia.
Qed.

(* 两因子合成：阈值内 N·(j+3) ≤ (j+2)·D，其中
   N = (n+j+1)³、D = (j+1)·(2n+j+2)²。铸法 = A、B 两因子按乘积序传递拼合。 *)
Lemma zb2_ga_ND_le : forall n j : nat,
  (1 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  Qle ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
       * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
      ((Z.of_nat (j + 2) # 1)
       * ((Z.of_nat (Datatypes.S j) # 1)
          * (Z.of_nat (2 * n + j + 2) # 1)
          * (Z.of_nat (2 * n + j + 2) # 1))).
Proof.
  intros n j Hn Hj Hsq.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_A_le n j)) as HA.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_B_le n j Hsq)) as HB.
  replace (j + 1)%nat with (Datatypes.S j)%nat in HB by lia.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (n + j + 1))) as Hn1.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (j + 3))) as Hj3.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (j + 2))) as Hj2.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (2 * n + j + 2))) as Hd22.
  pose proof (QleT'_to_Qle _ _ (zb2_ga_natpos_ge (Datatypes.S j))) as Hj1.
  assert (Ha0 : 0 <= (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
    by (apply Qmult_le_0_compat; assumption).
  assert (Hc0 : 0 <= (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1))
    by (apply Qmult_le_0_compat; assumption).
  assert (E1 : ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
                * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
             == ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
                * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
    by ring.
  rewrite E1.
  apply (Qle_trans
           (((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1))
            * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)))
           (((Z.of_nat (j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
            * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1)))).
  - apply (zb2_ga_mult_le _ _ _ _ Ha0 Hc0 HA HB).
  - assert (E : ((Z.of_nat (j + 2) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
                * ((Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (2 * n + j + 2) # 1))
             == (Z.of_nat (j + 2) # 1)
                * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)))
      by ring.
    rewrite E. apply Qle_refl.
Qed.

(* ===================================================================== *)
(* §4 阈值形逐档下降与单调                                                 *)
(* ===================================================================== *)

(* 逐档下降（交叉形）：阈值内 term(n, j+1)·(j+3) ≤ term(n, j)·(j+2)。
   铸法：比率律把左端尺度化到 term(j)·N·(j+3)，ND 不等式给
   N·(j+3) ≤ (j+2)·D，按乘积序传递后以 D > 0 取消。 *)
Theorem zb2_ga_term_step_le : forall n j : nat,
  (1 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  QleT' (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
        (zb2_term n j * (Z.of_nat (j + 2) # 1)).
Proof.
  intros n j Hn Hj Hsq. apply Qle_to_QleT'.
  assert (Hj1 : (1 <= Datatypes.S j)%nat) by lia.
  assert (Hd2 : (1 <= 2 * n + j + 2)%nat) by lia.
  pose proof (QltT_to_Qlt _ _ (zb2_ga_natpos_lt (Datatypes.S j) Hj1)) as Hj1p.
  pose proof (QltT_to_Qlt _ _ (zb2_ga_natpos_lt (2 * n + j + 2) Hd2)) as Hd2p.
  assert (HD : 0 < (Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; assumption.
    - exact Hd2p. }
  pose proof (qeqT_imp_qeq _ _ (zb2_ga_term_ratio n j)) as Hr.
  replace (n + Datatypes.S j + n + 1)%nat with (2 * n + j + 2)%nat in Hr by lia.
  replace (n + Datatypes.S j)%nat with (n + j + 1)%nat in Hr by lia.
  pose proof (zb2_ga_ND_le n j Hn Hj Hsq) as HN.
  pose proof (QltT_to_Qlt _ _ (zb2_term_pos n j)) as Htp.
  assert (Htp0 : 0 <= zb2_term n j) by (apply (Qlt_le_weak 0); exact Htp).
  assert (E1 : (zb2_term n (Datatypes.S j) * (Z.of_nat (j + 3) # 1))
               * ((Z.of_nat (Datatypes.S j) # 1)
                  * (Z.of_nat (2 * n + j + 2) # 1)
                  * (Z.of_nat (2 * n + j + 2) # 1))
            == (zb2_term n (Datatypes.S j)
                * ((Z.of_nat (Datatypes.S j) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)
                   * (Z.of_nat (2 * n + j + 2) # 1)))
               * (Z.of_nat (j + 3) # 1))
    by ring.
  assert (E2 : (zb2_term n j
                * ((Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (n + j + 1) # 1)
                   * (Z.of_nat (n + j + 1) # 1)))
               * (Z.of_nat (j + 3) # 1)
            == zb2_term n j
               * ((Z.of_nat (n + j + 1) # 1)
                  * (Z.of_nat (n + j + 1) # 1)
                  * (Z.of_nat (n + j + 1) # 1)
                  * (Z.of_nat (j + 3) # 1)))
    by ring.
  apply (zb2_ga_cancel_r _ _
           ((Z.of_nat (Datatypes.S j) # 1)
            * (Z.of_nat (2 * n + j + 2) # 1)
            * (Z.of_nat (2 * n + j + 2) # 1)) HD).
  apply (Qle_trans _ (zb2_term n j
        * ((Z.of_nat (n + j + 1) # 1) * (Z.of_nat (n + j + 1) # 1)
           * (Z.of_nat (n + j + 1) # 1) * (Z.of_nat (j + 3) # 1)))).
  - rewrite E1. rewrite Hr. rewrite E2. apply Qle_refl.
  - assert (HE : (zb2_term n j * (Z.of_nat (j + 2) # 1))
                 * ((Z.of_nat (Datatypes.S j) # 1)
                    * (Z.of_nat (2 * n + j + 2) # 1)
                    * (Z.of_nat (2 * n + j + 2) # 1))
              == zb2_term n j
                 * ((Z.of_nat (j + 2) # 1)
                    * ((Z.of_nat (Datatypes.S j) # 1)
                       * (Z.of_nat (2 * n + j + 2) # 1)
                       * (Z.of_nat (2 * n + j + 2) # 1))))
      by ring.
    rewrite HE.
    apply (zb2_ga_mult_le (zb2_term n j) (zb2_term n j)).
    + exact Htp0.
    + apply Qmult_le_0_compat.
      * apply Qmult_le_0_compat.
        -- apply Qmult_le_0_compat.
           ++ apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
           ++ apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
        -- apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (n + j + 1)).
      * apply QleT'_to_Qle. apply (zb2_ga_natpos_ge (j + 3)).
    + apply Qle_refl.
    + exact HN.
Qed.

(* 逐档单调（阈值内）：term(n, j+1) ≤ term(n, j)。
   铸法：下降式右端 term(j)·(j+2) ≤ term(j)·(j+3)（term(j) ≥ 0），
   再以 (j+3) > 0 取消。 *)
Theorem zb2_ga_term_mono_from : forall n j : nat,
  (1 <= n)%nat -> (2 <= j)%nat -> (n * n <= Datatypes.S j)%nat ->
  QleT' (zb2_term n (Datatypes.S j)) (zb2_term n j).
Proof.
  intros n j Hn Hj Hsq. apply Qle_to_QleT'.
  apply (zb2_ga_cancel_r _ _ (Z.of_nat (j + 3) # 1)).
  - apply QltT_to_Qlt. apply zb2_ga_natpos_lt. lia.
  - assert (Hj2 : Qle (Z.of_nat (j + 2) # 1) (Z.of_nat (j + 3) # 1))
      by (unfold Qle; cbn [Qnum Qden]; lia).
    pose proof (QltT_to_Qlt _ _ (zb2_term_pos n j)) as Htp.
    assert (Htp0 : 0 <= zb2_term n j) by (apply (Qlt_le_weak 0); exact Htp).
    assert (HEa : zb2_term n j * (Z.of_nat (j + 2) # 1)
               == (Z.of_nat (j + 2) # 1) * zb2_term n j) by ring.
    assert (HEb : zb2_term n j * (Z.of_nat (j + 3) # 1)
               == (Z.of_nat (j + 3) # 1) * zb2_term n j) by ring.
    apply (Qle_trans _ ((Z.of_nat (j + 2) # 1) * zb2_term n j)).
    + rewrite <- HEa. exact (QleT'_to_Qle _ _ (zb2_ga_term_step_le n j Hn Hj Hsq)).
    + rewrite HEb. exact (Qmult_le_compat_r (Z.of_nat (j + 2) # 1)
                                (Z.of_nat (j + 3) # 1) (zb2_term n j) Hj2 Htp0).
Qed.

(* 平移单调（阈值内）：J ≤ J+d ⟹ term(n, J+d+1) ≤ term(n, J)。
   对平移量 d 归纳，逐档以单调式回落。 *)
Theorem zb2_ga_term_drop : forall n d J : nat,
  (1 <= n)%nat -> (2 <= J)%nat -> (n * n <= Datatypes.S J)%nat ->
  QleT' (zb2_term n (Datatypes.S (J + d))) (zb2_term n J).
Proof.
  intros n d J Hn HJ2 Hsq. induction d as [| d IH].
  - replace (J + 0)%nat with J by lia.
    exact (zb2_ga_term_mono_from n J Hn HJ2 Hsq).
  - replace (J + Datatypes.S d)%nat with (Datatypes.S (J + d)) by lia.
    apply (qleT'_trans _ (zb2_term n (Datatypes.S (J + d)))).
    + apply (zb2_ga_term_mono_from n (Datatypes.S (J + d))).
      * exact Hn.
      * lia.
      * lia.
    + exact IH.
Qed.

(* ===================================================================== *)
(* §5 尾界机（S-2 验收「尾界 ≤ 显式 Q 式」·θ=1 收窄形）与对接形实例          *)
(* ===================================================================== *)

(* nat 后继的 Q 数值面：Z.of_nat (S k) #1 == 1 + Z.of_nat k #1 *)
Lemma zb2_ga_qsucc : forall k : nat,
  (Z.of_nat (Datatypes.S k) # 1) == 1 + (Z.of_nat k # 1).
Proof.
  intro k. unfold Qeq, Qplus. cbn [Qnum Qden].
  rewrite Nat2Z.inj_succ. lia.
Qed.

(* 尾界机：阈值 J 内起步，则任意 M ≥ J 的部分和被
   Isum(n, J) + (M−J)·term(n, J) 显式 Q 式封顶。
   对 M 归纳：步档以平移单调 term(n, S M) ≤ term(n, J) 收入余项。 *)
Theorem zb2_ga_Isum_tail_bound : forall n J M : nat,
  (J <= M)%nat -> (2 <= J)%nat -> (1 <= n)%nat -> (n * n <= Datatypes.S J)%nat ->
  QleT' (zb2_Isum n M)
        (zb2_Isum n J + (Z.of_nat (M - J) # 1) * zb2_term n J).
Proof.
  intros n J M HJM HJ2 Hn Hsq. apply Qle_to_QleT'.
  revert HJM. induction M as [| M IH]; intro HJM.
  - exfalso. lia.
  - destruct (Nat.eq_dec J (Datatypes.S M)) as [Heq | Hne].
    + subst J.
      assert (E : (Z.of_nat (Datatypes.S M - Datatypes.S M) # 1)
                  * zb2_term n (Datatypes.S M) == 0).
      { replace (Datatypes.S M - Datatypes.S M)%nat with 0%nat by lia.
        cbn [Z.of_nat]. ring. }
      rewrite E. rewrite Qplus_0_r. apply Qle_refl.
    + assert (HJM' : (J <= M)%nat) by lia.
      pose proof (IH HJM') as IHq.
      pose proof (QleT'_to_Qle _ _ (zb2_ga_term_drop n (M - J) J Hn HJ2 Hsq)) as Hdrop.
      replace (Datatypes.S (J + (M - J))) with (Datatypes.S M) in Hdrop by lia.
      cbn [zb2_Isum].
      assert (Hmul : (Z.of_nat (M - J) # 1) * zb2_term n J + zb2_term n J
                  == (Z.of_nat (Datatypes.S M - J) # 1) * zb2_term n J).
      { replace (Datatypes.S M - J)%nat with (Datatypes.S (M - J))%nat by lia.
        rewrite zb2_ga_qsucc. ring. }
      apply (Qle_trans _ (zb2_Isum n J
                          + (Z.of_nat (M - J) # 1) * zb2_term n J
                          + zb2_term n (Datatypes.S M))).
      * exact (Qplus_le_compat _ _ _ _ IHq (Qle_refl _)).
      * rewrite <- Hmul.
        rewrite <- Qplus_assoc.
        exact (Qplus_le_compat _ _ _ _ (Qle_refl _)
                 (Qplus_le_compat _ _ _ _ (Qle_refl _) Hdrop)).
Qed.

(* 对接形实例（sep_small 前提 II 同坐标）：n = S m、J = m²+2m
   （阈值 S J = m²+2m+1 = (S m)²），M ≥ J 时部分和显式封顶。
   本句即缺口件与装配面的入口指针形。 *)
Theorem zb2_ga_tail_at_sm : forall m M : nat,
  (8 <= m)%nat -> (m * m + 2 * m <= M)%nat ->
  QleT' (zb2_Isum (Datatypes.S m) M)
        (zb2_Isum (Datatypes.S m) (m * m + 2 * m)
         + (Z.of_nat (M - (m * m + 2 * m)) # 1)
           * zb2_term (Datatypes.S m) (m * m + 2 * m)).
Proof.
  intros m M Hm HM.
  apply (zb2_ga_Isum_tail_bound (Datatypes.S m) (m * m + 2 * m) M).
  - lia.
  - lia.
  - lia.
  - nia.
Qed.

(* ===================================================================== *)
(* §6 尾舱：主语句公理面自检                                               *)
(* ===================================================================== *)

Print Assumptions zb2_ga_bkC_step.
Print Assumptions zb2_ga_term_ratio.
Print Assumptions zb2_ga_A_le.
Print Assumptions zb2_ga_B_le.
Print Assumptions zb2_ga_ND_le.
Print Assumptions zb2_ga_term_step_le.
Print Assumptions zb2_ga_term_mono_from.
Print Assumptions zb2_ga_term_drop.
Print Assumptions zb2_ga_Isum_tail_bound.
Print Assumptions zb2_ga_tail_at_sm.
