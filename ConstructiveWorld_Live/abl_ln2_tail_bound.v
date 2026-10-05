(* ===================================================================== *)
(*  abl_ln2_tail_bound.v —— ln2 无理性链·Beukers 通道收敛桥+几何尾界件      *)
(*  使命: 「几何衰减不等式本体」的纯不等式核。机器实算判定：Beukers β 级数   *)
(*        bv_term 的 m-尾**无**一致几何比率（R(m) = (n+m+1)(n+2m+1)(n+2m+2)  *)
(*        /((m+1)(3n+2m+3)(3n+2m+4)) → 1；lnt_beta_rho_refuted34/1516 在    *)
(*        n=0,m=30 处 R=1891/2016>15/16>3/4 双点判定），故初版草案「尾和 ≤   *)
(*        C(n)·ρ^M」在 β 级数上不成立、须另择通道。真几何档建于 (2−t) 归一   *)
(*        化极点级数尾对象 u(n,k) = C(n+k,n)/((k+1)·2^{k+1})（逐项积分       *)
(*        ∫₀¹(t/2)^k dt = 1/((k+1)2^{k+1}），有限 M 换序恒等式的尾项控制件）:*)
(*        一致比率 u(n,k+1)/u(n,k) = (n+k+1)/(2(k+2)) ≤ 3/4 ⟺ 2n ≤ k+4，    *)
(*        由此闭合 比率档 lnt_pterm_ratio → 幂式档 lnt_pterm_pow → 几何部分  *)
(*        和 lnt_geo_partial → 部分和隙 Cauchy 模量 lnt_pterm_gap → 峰值档  *)
(*        lnt_pterm_peak → 组合终形 lnt_gap_geo：尾隙 ≤ 2^{n+1}·(3/4)^{SM−2n}*)
(*        （C(n)·ρ^M 形，ρ=3/4）。β 侧交付: 精确交叉比率恒等式 lnt_bv_cross  *)
(*        （rx_term_decayQ 单调档定量升级，供下游亏量账）＋亏量显式全正展开  *)
(*        lnt_deficit_pos（n≤m 窗）。                                        *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-    *)
(*        Complete S03_QExp PolyIntegral PadeErrorIntegral BeukersLists     *)
(*        BeukersVariant PintMono PsQReindex（rx_bkC_ratio/rx_Qlt_Z1 使用）。*)
(*  对标: Beukers 1979 ln2 无理性积分证明的级数尾控制（论文 3 附录 E        *)
(*        开放项(b) 收敛桥的输入侧核件）；PsQReindex rx_term_decayQ 的      *)
(*        几何率升级；Ln2Bridge ln2b_escape_of_supply 前提的改型对应件。     *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（QeqT/QltT/QleT'），nat 层核   *)
(*        全 lia/ring 显式展开；Qeq/Qle/Qlt 支撑引理仅 Prop 面作推理；      *)
(*        ==-重写一律限于 == 目标内、Qle 目标换形走 qeq_le/Qle_trans 显式   *)
(*        传送；文尾 Print Assumptions 全 Closed＋独立提取验证。            *)
(*  编译配方: rocq c -native-compiler no -Q vo_local_world_unified_0930     *)
(*        ""（编译目录 ln2_tail/，并发限 1）。                               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 通用小工器：Qeq 桥、除消、2 幂正性、几何常数面                     *)
(* ============================================================ *)

(* Qeq 桥（QleT' 两侧换形；换形经 Qle_trans/qeq_le 显式传送） *)
Lemma lnt_leT'_eq_l : forall x y z : Q, x == y -> QleT' x z -> QleT' y z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans y x z).
  - apply qeq_le. apply Qeq_sym. exact H.
  - apply QleT'_to_Qle. exact Hq.
Qed.

Lemma lnt_leT'_eq_r : forall x y z : Q, y == z -> QleT' x y -> QleT' x z.
Proof.
  intros x y z H Hq. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact Hq.
  - apply qeq_le. exact H.
Qed.

(* Qeq 基非零（本环境的 Q <> 0 为 Qeq 基） *)
Lemma lnt_qneq_of_eq0 : forall x : Q, Qlt 0 x -> ~ (x == 0%Q).
Proof.
  intros x H HC. apply (Qlt_not_eq 0%Q x H). rewrite HC. reflexivity.
Qed.

(* 正因子右乘除消：0 < z 且 x·z ≤ y·z ⟹ x ≤ y（Prop 面） *)
Lemma lnt_qle_mul_cancel_r : forall (x y z : Q),
  Qlt 0 z -> Qle (x * z) (y * z) -> Qle x y.
Proof.
  intros x y z Hz Hle.
  assert (Hzn : ~ (z == 0%Q)) by (apply lnt_qneq_of_eq0; exact Hz).
  assert (Hzinv : (z * Qinv z)%Q == 1%Q) by (apply Qmult_inv_r; exact Hzn).
  assert (E1 : x == x * z * Qinv z).
  { rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hzn.
    rewrite Qmult_1_r. reflexivity. }
  assert (E2 : Qle (y * z * Qinv z) y).
  { assert (H1 : (y * z * Qinv z)%Q == y%Q).
    { rewrite <- Qmult_assoc. rewrite Qmult_inv_r by exact Hzn.
      rewrite Qmult_1_r. reflexivity. }
    apply rx_Qeq_le. exact H1. }
  apply (Qle_trans x (x * z * Qinv z)%Q y).
  - apply qeq_le. exact E1.
  - apply (Qle_trans (x * z * Qinv z)%Q (y * z * Qinv z)%Q y).
    + apply Qmult_le_compat_r.
      * exact Hle.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hz.
    + exact E2.
Qed.

(* 左乘保序（stdlib 缺 Qmult_le_compat_l 的本件补件） *)
Lemma lnt_Qmult_le_compat_l : forall (x y z : Q),
  Qle 0 z -> Qle x y -> Qle (z * x) (z * y).
Proof.
  intros x y z Hz Hxy.
  apply (Qle_trans (z * x) (x * z) (z * y)).
  - apply qeq_le. ring.
  - apply (Qle_trans (x * z) (y * z) (z * y)).
    + apply Qmult_le_compat_r; assumption.
    + apply qeq_le. ring.
Qed.

Lemma lnt_qinv_mul_cancel : forall z : Q, ~ (z == 0%Q) -> Qinv z * z == 1.
Proof.
  intros z Hz. rewrite Qmult_comm. apply Qmult_inv_r. exact Hz.
Qed.

Lemma lnt_pow2_pos : forall j : nat, Qlt 0 (q_pow (2 # 1)%Q j).
Proof.
  induction j as [| j IH].
  - apply rx_Qlt_Z1. lia.
  - rewrite q_pow_succ. apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + exact IH.
Qed.

Lemma lnt_q4_le0 : QleT' 0 (4 # 1)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. Qed.

Lemma lnt_rho_le0 : QleT' 0 (3 # 4)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. Qed.

Lemma lnt_pow_pos_le : forall d : nat, QleT' 0 (q_pow (3 # 4)%Q d).
Proof.
  induction d as [| d IH].
  - cbn [q_pow]. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
  - apply lnt_leT'_eq_r with (y := ((3 # 4)%Q * q_pow (3 # 4)%Q d)%Q).
    + rewrite q_pow_succ. ring.
    + apply lnt_leT'_eq_l with (x := (0 * q_pow (3 # 4)%Q d)%Q).
      * ring.
      * apply qleT'_mult_compat_r; [exact IH | apply lnt_rho_le0].
Qed.

(* 1 − x ≤ 1（由 0 ≤ x） *)
Lemma lnt_sub_le1 : forall x : Q, QleT' 0 x -> QleT' (1 - x)%Q 1%Q.
Proof.
  intros x Hx. apply Qle_to_QleT'.
  apply (Qle_trans ((1 + (- x))%Q) ((1 + 0)%Q) 1%Q).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply (Qle_trans (- x) ((- x) + x) 0%Q).
      * apply (Qle_trans (- x) ((- x) + 0) ((- x) + x)).
        -- apply qeq_le. apply Qeq_sym. ring.
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply QleT'_to_Qle. exact Hx.
      * assert (Er2 : ((- x) + x)%Q == 0%Q) by ring.
        apply qeq_le. exact Er2.
  - assert (H1 : 1%Q == (1 + 0)%Q) by ring.
    apply qeq_le. apply Qeq_sym. exact H1.
Qed.

(* q_pow (2#1) j 的 Z.of_nat 桥 *)
Lemma lnt_qpow_Zofnat : forall j : nat,
  q_pow (2 # 1)%Q j == (Z.of_nat (2 ^ j) # 1)%Q.
Proof.
  induction j as [| j IH].
  - reflexivity.
  - rewrite q_pow_succ, IH.
    change (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat.
    replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
    apply bk_Qmul_nat.
Qed.

(* ============================================================ *)
(* §A nat 层核：极点比率窗口键、β 亏量显式全正展开、bkC 二幂上界         *)
(* ============================================================ *)

(* 窗口键：2n ≤ k+4 ⟹ 2(n+k+1) ≤ 3(k+2)（等价于比率 ≤ 3/4） *)
Lemma lnt_key_pole : forall n k : nat,
  2 * n <= k + 4 -> 2 * (n + Datatypes.S k) <= 3 * (Datatypes.S (Datatypes.S k)).
Proof. intros n k H. lia. Qed.

(* β 亏量（n ≤ m 窗）：分母积 − 分子积 = 全正展开多项式（7n³+12n²d+4nd²+…） *)
Theorem lnt_deficit_pos : forall n m : nat,
  n <= m ->
  (n + m + 1) * (n + 2 * m + 1) * (n + 2 * m + 2)
  < (m + 1) * (3 * n + 2 * m + 3) * (3 * n + 2 * m + 4).
Proof.
  intros n m Hnm.
  assert (Hd : exists d : nat, m = n + d) by (exists (m - n); lia).
  destruct Hd as [d Hd]. subst m.
  assert (Hexp : (n + d + 1) * (3 * n + 2 * (n + d) + 3) * (3 * n + 2 * (n + d) + 4)
               = (n + (n + d) + 1) * (n + 2 * (n + d) + 1) * (n + 2 * (n + d) + 2)
                 + (7 * (n * n * n) + 12 * (n * n) * d + 4 * n * (d * d)
                    + 8 * (d * d) + 36 * n * d + 33 * (n * n) + 18 * d + 34 * n + 10))
    by ring.
  rewrite Hexp. lia.
Qed.

(* 二幂下界：1 ≤ 2^N（供 lia 以 2^N 为原子闭合上界组合） *)
Lemma lnt_pow2_ge1 : forall N : nat, 1 <= 2 ^ N.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [Nat.pow]. lia.
Qed.

(* bkC 二幂上界：k ≤ N ⟹ C(N,k) ≤ 2^N（Pascal 归纳，行和上界） *)
Lemma lnt_bkC_le_pow2 : forall N k : nat, k <= N -> bkC N k <= 2 ^ N.
Proof.
  induction N as [| N IH]; intros k Hk.
  - assert (Hk0 : k = 0) by lia. subst k.
    cbn [bkC Nat.pow]. lia.
  - destruct k as [| k'].
    + cbn [bkC Nat.pow]. assert (Hg := lnt_pow2_ge1 N). lia.
    + assert (Hk' : k' <= N) by lia.
      assert (H1 := IH k' Hk').
      destruct (le_lt_dec (Datatypes.S k') N) as [Hs | Hl].
      * assert (H2 := IH (Datatypes.S k') Hs).
        cbn [bkC Nat.pow]. assert (Hg := lnt_pow2_ge1 N). lia.
      * assert (H0 : bkC N (Datatypes.S k') = 0) by (apply bkC_out; lia).
        cbn [bkC Nat.pow]. rewrite H0.
        assert (Hg := lnt_pow2_ge1 N). lia.
Qed.

(* rx_bkC_ratio 的本件移形实例 *)
Lemma lnt_bkC_step : forall n m : nat,
  bkC (Datatypes.S (n + m)) n * Datatypes.S m = bkC (n + m) n * (n + Datatypes.S m).
Proof.
  intros n m.
  assert (Hsm : Datatypes.S (n + m) = n + Datatypes.S m) by lia.
  rewrite Hsm.
  assert (H1 := rx_bkC_ratio (n + m) n (Nat.le_add_r n m)).
  replace (Datatypes.S (n + m) - n) with (Datatypes.S m) in H1 by lia.
  rewrite Hsm in H1. exact H1.
Qed.

(* ============================================================ *)
(* §B 极点级数尾对象：(2−t) 归一化展开的全正项族与其几何率档             *)
(*     u(n,k) = C(n+k,n) / ((k+1)·2^{k+1})                               *)
(* ============================================================ *)

Definition lnt_pterm (n k : nat) : Q :=
  ((Z.of_nat (bkC (n + k) n) # 1) /
     ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

Theorem lnt_pterm_pos : forall n k : nat, QltT 0 (lnt_pterm n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold lnt_pterm, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : 1 <= bkC (n + k) n) by (apply bkC_pos; lia).
    assert (Hz : (0 <= Z.of_nat (bkC (n + k) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + apply lnt_pow2_pos.
Qed.

(** 核心①比率档：2n ≤ k+4 ⟹ u(n,k+1) ≤ (3/4)·u(n,k)。
    代数：u(n,k+1)/u(n,k) = (n+k+1)/(2(k+2))，窗口键 2(n+k+1) ≤ 3(k+2)。 *)
Theorem lnt_pterm_ratio : forall n k : nat,
  2 * n <= k + 4 -> QleT' (lnt_pterm n (Datatypes.S k)) ((3 # 4)%Q * lnt_pterm n k).
Proof.
  intros n k H. apply Qle_to_QleT'.
  assert (HsS : lnt_pterm n (Datatypes.S k)
    == ((Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) *
                ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S k))))%Q).
  { unfold lnt_pterm, Qdiv.
    replace (n + Datatypes.S k) with (Datatypes.S (n + k)) by lia.
    rewrite (q_pow_succ (2 # 1)%Q (Datatypes.S k)). reflexivity. }
  assert (HsT : lnt_pterm n k
    == ((Z.of_nat (bkC (n + k) n) # 1) *
          Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
  { unfold lnt_pterm, Qdiv. reflexivity. }
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + k)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + k) n) # 1)%Q).
  set (a1 := (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)%Q).
  set (a0 := (Z.of_nat (Datatypes.S k) # 1)%Q).
  set (Qp := q_pow (2 # 1)%Q (Datatypes.S k)).
  assert (Ha1 : Qlt 0 a1) by (apply rx_Qlt_Z1; lia).
  assert (Ha0 : Qlt 0 a0) by (apply rx_Qlt_Z1; lia).
  assert (HQp : Qlt 0 Qp) by apply lnt_pow2_pos.
  assert (Ha1HQ : Qlt 0 (a1 * ((2 # 1)%Q * Qp))%Q)
    by (apply Qmult_lt_0_compat; [exact Ha1 | apply Qmult_lt_0_compat;
         [apply rx_Qlt_Z1; lia | exact HQp]]).
  assert (Ha0Q : Qlt 0 (a0 * Qp)%Q) by (apply Qmult_lt_0_compat; assumption).
  (* nat 核：2·C1·(S k) ≤ 3·C0·(S (S k))（经窗口键 + bkC 移形） *)
  assert (Hnat : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k
               <= 3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)).
  { assert (Hkey := lnt_key_pole n k H).
    assert (Hstep := lnt_bkC_step n k).
    assert (Hm := Nat.mul_le_mono_l (2 * (n + Datatypes.S k))
                  (3 * Datatypes.S (Datatypes.S k)) (bkC (n + k) n) Hkey).
    assert (HeqL : 2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k
                 = bkC (n + k) n * (2 * (n + Datatypes.S k))).
    { replace (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k)
        with (2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) by ring.
      rewrite Hstep. ring. }
    assert (HeqR : 3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)
                 = bkC (n + k) n * (3 * Datatypes.S (Datatypes.S k))) by ring.
    rewrite HeqL, HeqR. exact Hm. }
  assert (HQcore : Qle ((2 # 1)%Q * C1 * a0) ((3 # 1)%Q * C0 * a1)).
  { assert (H1 : Qle ((Z.of_nat (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1)%Q)
                     ((Z.of_nat (3 * bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1)%Q))
      by (apply bk_Qle_nat; exact Hnat).
    assert (HassocL : (2 * bkC (Datatypes.S (n + k)) n * Datatypes.S k)
                    = 2 * (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) by ring.
    assert (HassocR : (3 * bkC (n + k) n * Datatypes.S (Datatypes.S k))
                    = 3 * (bkC (n + k) n * Datatypes.S (Datatypes.S k))) by ring.
    rewrite HassocL, HassocR in H1.
    assert (E1 : (Z.of_nat (bkC (Datatypes.S (n + k)) n * Datatypes.S k) # 1)%Q
                 == (C1 * a0)%Q) by (symmetry; apply bk_Qmul_nat).
    assert (E2 : (Z.of_nat (bkC (n + k) n * Datatypes.S (Datatypes.S k)) # 1)%Q
                 == (C0 * a1)%Q) by (symmetry; apply bk_Qmul_nat).
    rewrite <- (bk_Qmul_nat 2 (bkC (Datatypes.S (n + k)) n * Datatypes.S k)) in H1.
    rewrite <- (bk_Qmul_nat 3 (bkC (n + k) n * Datatypes.S (Datatypes.S k))) in H1.
    rewrite E1, E2 in H1.
    change (Z.of_nat 2 # 1)%Q with (2 # 1)%Q in H1.
    change (Z.of_nat 3 # 1)%Q with (3 # 1)%Q in H1.
    assert (E3 : ((2 # 1)%Q * (C1 * a0))%Q == ((2 # 1)%Q * C1 * a0)%Q) by ring.
    assert (E4 : ((3 # 1)%Q * (C0 * a1))%Q == ((3 # 1)%Q * C0 * a1)%Q) by ring.
    rewrite E3, E4 in H1. exact H1. }
  (* 爆开形 Qle（除消链核心）：x := C1·Qinv(a1·(2·Qp)) ≤ y := (3/4)·(C0·Qinv(a0·Qp)) *)
  assert (Hmain : Qle ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
                      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)).
  { assert (Hxz : ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == (C1 * (a0 * Qp))%Q).
    { assert (Hcert : Qinv (a1 * ((2 # 1)%Q * Qp))
                        * (a1 * ((2 # 1)%Q * Qp)) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha1HQ).
      rewrite <- Qmult_assoc.
      transitivity (C1 * ((Qinv (a1 * ((2 # 1)%Q * Qp))
                            * (a1 * ((2 # 1)%Q * Qp))) * (a0 * Qp)))%Q.
      - ring.
      - rewrite Hcert. ring. }
    assert (Hyz : (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                     * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                 == ((3 # 4)%Q * C0 * a1 * ((2 # 1)%Q * Qp))%Q).
    { assert (Hcert0 : Qinv (a0 * Qp) * (a0 * Qp) == 1%Q)
        by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Ha0Q).
      rewrite <- Qmult_assoc, <- Qmult_assoc.
      transitivity ((3 # 4)%Q * C0
                      * ((Qinv (a0 * Qp) * (a0 * Qp))
                           * (a1 * ((2 # 1)%Q * Qp))))%Q.
      - ring.
      - rewrite Hcert0. ring. }
    apply (lnt_qle_mul_cancel_r
      ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q)
      (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q)
      (((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp))%Q)).
    - apply Qmult_lt_0_compat; [exact Ha1HQ | exact Ha0Q].
    - apply (Qle_trans ((C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
                (C1 * (a0 * Qp))%Q
                (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                    * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q).
      + apply qeq_le. exact Hxz.
      + apply (lnt_qle_mul_cancel_r (C1 * (a0 * Qp))%Q
          (((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
             * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))%Q
          (((2 # 1)%Q * Qp))%Q).
        * apply Qmult_lt_0_compat;
            [apply rx_Qlt_Z1; lia | exact HQp].
        * apply (Qle_trans ((C1 * (a0 * Qp)) * ((2 # 1)%Q * Qp))%Q
                   (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                   ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                       * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                      * ((2 # 1)%Q * Qp))%Q).
          -- apply qeq_le. ring.
          -- apply (Qle_trans (((2 # 1)%Q * C1 * a0) * (Qp * Qp))%Q
                     (((3 # 1)%Q * C0 * a1) * (Qp * Qp))%Q
                     ((((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))
                          * ((a1 * ((2 # 1)%Q * Qp)) * (a0 * Qp)))
                         * ((2 # 1)%Q * Qp))%Q).
             ++ apply Qmult_le_compat_r.
                ** exact HQcore.
                ** apply Qlt_le_weak. apply Qmult_lt_0_compat; exact HQp.
             ++ apply qeq_le. rewrite Hyz. ring. }
  (* 三段传送：爆开形与 lnt_pterm 形的 == 桥 + Hmain *)
  apply (Qle_trans (lnt_pterm n (Datatypes.S k))
           (C1 * Qinv (a1 * ((2 # 1)%Q * Qp)))%Q
           ((3 # 4)%Q * lnt_pterm n k)%Q).
  - apply qeq_le. exact HsS.
  - apply (Qle_trans _ ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q _).
    + exact Hmain.
    + apply qeq_le.
      assert (Ey : ((3 # 4)%Q * (C0 * Qinv (a0 * Qp)))%Q
                 == ((3 # 4)%Q * lnt_pterm n k)%Q).
      { rewrite HsT. apply Qeq_refl. }
      exact Ey.
Qed.

(** 核心②幂式档：u(n,k+j) ≤ u(n,k)·(3/4)^j。 *)
Theorem lnt_pterm_pow : forall (n k j : nat),
  2 * n <= k + 4 -> QleT' (lnt_pterm n (k + j))
    ((lnt_pterm n k * q_pow (3 # 4)%Q j)%Q).
Proof.
  intros n k j H. induction j as [| j IH].
  - apply lnt_leT'_eq_r with (y := (lnt_pterm n k * 1)%Q).
    + cbn [q_pow]. rewrite Qmult_1_r. apply Qeq_refl.
    + apply qeq_leT'. replace (k + 0) with k by lia.
      rewrite Qmult_1_r. apply Qeq_refl.
  - apply lnt_leT'_eq_r with
      (y := (lnt_pterm n k * ((3 # 4)%Q * q_pow (3 # 4)%Q j))%Q).
    + rewrite q_pow_succ. ring.
    + apply qleT'_trans with ((3 # 4)%Q * lnt_pterm n (k + j))%Q.
      * replace (k + Datatypes.S j) with (Datatypes.S (k + j)) by lia.
        apply lnt_pterm_ratio. lia.
      * apply lnt_leT'_eq_r with
          (y := ((3 # 4)%Q * (lnt_pterm n k * q_pow (3 # 4)%Q j))%Q).
        -- ring.
        -- apply (qleT'_mult_compat_l (lnt_pterm n (k + j))
                    (lnt_pterm n k * q_pow (3 # 4)%Q j) (3 # 4)%Q
                    lnt_rho_le0 IH).
Qed.

(** 核心③几何部分和精确恒等式：Σ_{i<d} (3/4)^i == 4·(1−(3/4)^d)。 *)
Theorem lnt_geo_partial : forall d : nat,
  sum_upto d (fun i : nat => q_pow (3 # 4)%Q i)
  == (4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q.
Proof.
  induction d as [| d IH].
  - cbn [sum_upto q_pow]. ring.
  - cbn [sum_upto]. rewrite q_pow_succ, IH. ring.
Qed.

(* 有限和三工器：逐点 ≤ 传送、公因子外提、范围裂分 *)
Lemma lnt_sum_le : forall (d : nat) (f g : nat -> Q),
  (forall i : nat, i < d -> QleT' (f i) (g i)) ->
  QleT' (sum_upto d f) (sum_upto d g).
Proof.
  intros d. induction d as [| d IH]; intros f g Hpt.
  - cbn [sum_upto]. apply qleT'_refl.
  - cbn [sum_upto]. apply qleT'_plus_compat.
    + apply IH. intros i Hi. apply Hpt. lia.
    + apply Hpt. lia.
Qed.

Lemma lnt_sum_scale : forall (d : nat) (c : Q) (h : nat -> Q),
  sum_upto d (fun i : nat => (c * h i)%Q) == (c * sum_upto d h)%Q.
Proof.
  induction d as [| d IH]; intros c h.
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

Lemma lnt_sum_range : forall (d M : nat) (f : nat -> Q),
  sum_upto (Datatypes.S (M + d)) f
  == sum_upto (Datatypes.S M) f + sum_upto d (fun i : nat => f (M + Datatypes.S i)).
Proof.
  induction d as [| d IH]; intros M f.
  - replace (M + 0) with M by lia. cbn [sum_upto].
    rewrite Qplus_0_r. apply Qeq_refl.
  - cbn [sum_upto].
    replace (M + Datatypes.S d) with (Datatypes.S (M + d)) by lia.
    rewrite IH.
    rewrite <- Qplus_assoc. apply Qeq_refl.
Qed.

(** 核心④尾项控制（Cauchy 模量核）：Σ_{i<d} u(n,M+1+i) ≤ 4·u(n,M+1)。 *)
Theorem lnt_pterm_tail : forall (n M d : nat),
  2 * n <= M + 4 ->
  QleT' (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
        ((4 # 1)%Q * lnt_pterm n (Datatypes.S M)).
Proof.
  intros n M d H.
  apply qleT'_trans with
    (lnt_pterm n (Datatypes.S M)
       * ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q))%Q.
  - apply lnt_leT'_eq_r with
      (y := sum_upto d (fun i : nat =>
                              (lnt_pterm n (Datatypes.S M)
                                  * q_pow (3 # 4)%Q i)%Q)).
    + rewrite lnt_sum_scale, lnt_geo_partial. apply Qeq_refl.
    + apply lnt_sum_le. intros i Hi.
      apply (qleT'_trans (lnt_pterm n (M + Datatypes.S i))
              (lnt_pterm n (Datatypes.S M + i))
              (lnt_pterm n (Datatypes.S M) * q_pow (3 # 4)%Q i)).
      * apply qeq_leT'.
        replace (M + Datatypes.S i) with (Datatypes.S M + i) by lia.
        apply Qeq_refl.
      * apply lnt_pterm_pow. lia.
  - apply qleT'_trans with
      (lnt_pterm n (Datatypes.S M) * ((4 # 1)%Q * 1)%Q)%Q.
    + apply (qleT'_mult_compat_l ((4 # 1)%Q * (1 - q_pow (3 # 4)%Q d)%Q)
               ((4 # 1)%Q * 1)%Q (lnt_pterm n (Datatypes.S M))).
      * apply qltT_leT'. apply lnt_pterm_pos.
      * apply qleT'_mult_compat_l.
        { apply lnt_q4_le0. }
        { apply lnt_sub_le1. apply lnt_pow_pos_le. }
    + apply qeq_leT'. ring.
Qed.

(** 核心⑤部分和隙（收敛桥 Cauchy 模量）：S_{M+d} − S_M ≤ 4·u(n,M+1) 的加法形。 *)
Theorem lnt_pterm_gap : forall (n M d : nat),
  2 * n <= M + 4 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
           + (4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q.
Proof.
  intros n M d H.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
    (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + (4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply Qle_to_QleT'.
    apply (Qplus_le_compat
      (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k))
      (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k))
      (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
      ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q).
    + apply Qle_refl.
    + apply QleT'_to_Qle. apply lnt_pterm_tail. exact H.
Qed.

(** 核心⑥绝对峰值档：1 ≤ n ⟹ u(n,k) ≤ 2^{n−1}（bkC ≤ 2^{n+k} 传送）。 *)
Theorem lnt_pterm_peak : forall n k : nat,
  1 <= n -> QleT' (lnt_pterm n k) (q_pow (2 # 1)%Q (n - 1)).
Proof.
  intros n k Hn. apply Qle_to_QleT'.
  assert (Ha0 : Qlt 0 (Z.of_nat (Datatypes.S k) # 1)%Q) by (apply rx_Qlt_Z1; lia).
  assert (HQp : Qlt 0 (q_pow (2 # 1)%Q (Datatypes.S k))) by apply lnt_pow2_pos.
  assert (Haz : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1)
                         * q_pow (2 # 1)%Q (Datatypes.S k))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  apply (lnt_qle_mul_cancel_r
    ((Z.of_nat (bkC (n + k) n) # 1) *
       Qinv ((Z.of_nat (Datatypes.S k) # 1) *
           q_pow (2 # 1)%Q (Datatypes.S k)))%Q
    (q_pow (2 # 1)%Q (n - 1))
    ((Z.of_nat (Datatypes.S k) # 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q).
  - exact Haz.
  - assert (Hcert : Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                            q_pow (2 # 1)%Q (Datatypes.S k))
                       * ((Z.of_nat (Datatypes.S k) # 1) *
                            q_pow (2 # 1)%Q (Datatypes.S k)) == 1%Q)
      by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Haz).
    apply (Qle_trans (((Z.of_nat (bkC (n + k) n) # 1) *
                          Qinv ((Z.of_nat (Datatypes.S k) # 1) *
                              q_pow (2 # 1)%Q (Datatypes.S k)))
                         * ((Z.of_nat (Datatypes.S k) # 1) *
                              q_pow (2 # 1)%Q (Datatypes.S k)))%Q
                (Z.of_nat (bkC (n + k) n) # 1)%Q
                ((q_pow (2 # 1)%Q (n - 1) *
                    ((Z.of_nat (Datatypes.S k) # 1) *
                        q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
    + apply qeq_le.
      transitivity ((Z.of_nat (bkC (n + k) n) # 1) *
        (Qinv ((Z.of_nat (Datatypes.S k) # 1) *
            q_pow (2 # 1)%Q (Datatypes.S k)) *
          ((Z.of_nat (Datatypes.S k) # 1) *
            q_pow (2 # 1)%Q (Datatypes.S k))))%Q.
      * ring.
      * rewrite Hcert. ring.
    + assert (Hbr : (Z.of_nat (2 ^ (n + k)) # 1)%Q
                    == (q_pow (2 # 1)%Q (n - 1) *
                          q_pow (2 # 1)%Q (Datatypes.S k))%Q).
      { replace (n + k) with ((n - 1) + Datatypes.S k) by lia.
        rewrite <- lnt_qpow_Zofnat, q_pow_add. reflexivity. }
      apply (Qle_trans (Z.of_nat (bkC (n + k) n) # 1)%Q
              (Z.of_nat (2 ^ (n + k)) # 1)%Q
              ((q_pow (2 # 1)%Q (n - 1) *
                  ((Z.of_nat (Datatypes.S k) # 1) *
                      q_pow (2 # 1)%Q (Datatypes.S k)))%Q)).
      * apply bk_Qle_nat. apply lnt_bkC_le_pow2. lia.
      * apply (Qle_trans _ (q_pow (2 # 1)%Q (n - 1) *
                               q_pow (2 # 1)%Q (Datatypes.S k))%Q _).
        -- apply qeq_le. exact Hbr.
        -- apply (Qle_trans
              (q_pow (2 # 1)%Q (n - 1) * q_pow (2 # 1)%Q (Datatypes.S k))%Q
              (q_pow (2 # 1)%Q (n - 1) *
                 (1 * q_pow (2 # 1)%Q (Datatypes.S k)))%Q
              (q_pow (2 # 1)%Q (n - 1) *
                 ((Z.of_nat (Datatypes.S k) # 1) *
                    q_pow (2 # 1)%Q (Datatypes.S k)))%Q).
           ++ apply lnt_Qmult_le_compat_l.
              ** apply Qlt_le_weak. apply lnt_pow2_pos.
              ** apply qeq_le. ring.
           ++ apply lnt_Qmult_le_compat_l.
              ** apply Qlt_le_weak. apply lnt_pow2_pos.
              ** assert (H1a0 : Qle 1 (Z.of_nat (Datatypes.S k) # 1)%Q)
                   by (apply (bk_Qle_nat 1 (Datatypes.S k)); lia).
                 apply Qmult_le_compat_r;
                   [exact H1a0 | apply Qlt_le_weak; exact HQp].
Qed.

Theorem lnt_gap_geo : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnt_pterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S n)
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    (sum_upto (Datatypes.S M) (fun k : nat => lnt_pterm n k)
       + ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q)%Q.
  - apply lnt_pterm_gap. lia.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + assert (Hpow := lnt_pterm_pow n (2 * n) (Datatypes.S M - 2 * n) ltac:(lia)).
      replace (2 * n + (Datatypes.S M - 2 * n)) with (Datatypes.S M) in Hpow
        by lia.
      assert (Hpk : QleT' (lnt_pterm n (2 * n)) (q_pow (2 # 1)%Q (n - 1)))
        by (apply lnt_pterm_peak; exact Hn).
      assert (Hchain : QleT' (lnt_pterm n (Datatypes.S M))
                         (q_pow (2 # 1)%Q (n - 1)
                            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))).
      { apply qleT'_trans with
          ((lnt_pterm n (2 * n)) * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q.
        - exact Hpow.
        - apply (qleT'_mult_compat_r (lnt_pterm n (2 * n))
                   (q_pow (2 # 1)%Q (n - 1))
                   (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
                   (lnt_pow_pos_le (Datatypes.S M - 2 * n)) Hpk). }
      assert (Hxy : QleT' ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))
                      ((4 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
                          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q).
      { apply (qleT'_mult_compat_l (lnt_pterm n (Datatypes.S M))
                 (q_pow (2 # 1)%Q (n - 1)
                    * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)) (4 # 1)%Q
                 lnt_rho_le0 Hchain). }
      assert (E42 : ((4 # 1)%Q * q_pow (2 # 1)%Q (n - 1))%Q
                    == q_pow (2 # 1)%Q (Datatypes.S n)).
      { replace (Datatypes.S n) with (2 + (n - 1)) by lia.
        rewrite q_pow_add. cbn [q_pow]. ring. }
      apply (lnt_leT'_eq_r
        ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q
        ((4 # 1)%Q * (q_pow (2 # 1)%Q (n - 1)
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q
        ((q_pow (2 # 1)%Q (Datatypes.S n)) *
            q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
      * rewrite <- E42. ring.
      * exact Hxy.
Qed.

(* ============================================================ *)
(* §C β 级数（bv_term）侧：精确交叉比率恒等式＋几何比率反例机器判定         *)
(* ============================================================ *)

(** 精确交叉比率恒等式（rx_term_decayQ 单调档的定量升级）：
    T(n,m+1)·(m+1)(3n+2m+3)(3n+2m+4) == T(n,m)·(n+m+1)(n+2m+1)(n+2m+2)。 *)
Theorem lnt_bv_cross : forall n m : nat,
  QeqT ((bv_term n (Datatypes.S m)
          * (Z.of_nat (Datatypes.S m * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)%Q)%Q)
       ((bv_term n m
          * (Z.of_nat ((n + m + 1) * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)%Q)%Q).
Proof.
  intros n m. apply qeq_imp_qeqT.
  assert (HshapeS : bv_term n (Datatypes.S m)
    == ((Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1) *
          ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1) *
             ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))))
        * (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))%Q).
  { unfold bv_term, Qdiv.
    replace (n + Datatypes.S m) with (Datatypes.S (n + m)) by lia.
    replace (n + 2 * Datatypes.S m) with (Datatypes.S (Datatypes.S (n + 2 * m))) by lia.
    replace (3 * n + 2 * Datatypes.S m + 2)
      with (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2))) by lia.
    rewrite (q_fact_succ (Datatypes.S (n + 2 * m))), (q_fact_succ (n + 2 * m)).
    rewrite (q_fact_succ (Datatypes.S (3 * n + 2 * m + 2))),
            (q_fact_succ (3 * n + 2 * m + 2)).
    rewrite !Qinv_mult_distr.
    replace (Datatypes.S (Datatypes.S (n + 2 * m))) with (n + 2 * m + 2) by lia.
    replace (Datatypes.S (n + 2 * m)) with (n + 2 * m + 1) by lia.
    replace (Datatypes.S (Datatypes.S (3 * n + 2 * m + 2)))
      with (3 * n + 2 * m + 4) by lia.
    replace (Datatypes.S (3 * n + 2 * m + 2)) with (3 * n + 2 * m + 3) by lia.
    ring. }
  assert (HshapeT : bv_term n m
    == (Z.of_nat (bkC (n + m) n) # 1) *
         (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2))%Q).
  { unfold bv_term, Qdiv. reflexivity. }
  rewrite HshapeS, HshapeT.
  set (C1 := (Z.of_nat (bkC (Datatypes.S (n + m)) n) # 1)%Q).
  set (C0 := (Z.of_nat (bkC (n + m) n) # 1)%Q).
  set (CF := (q_fact (n + 2 * m) * q_fact (2 * n + 1)
                 / q_fact (3 * n + 2 * m + 2))%Q).
  set (Jp := ((1 / (Z.of_nat (3 * n + 2 * m + 3) # 1))
                * (1 / (Z.of_nat (3 * n + 2 * m + 4) # 1)))%Q).
  set (cd := (Z.of_nat ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4)) # 1)%Q).
  assert (Hc3 : Qlt 0 (Z.of_nat (3 * n + 2 * m + 3) # 1)%Q) by (apply rx_Qlt_Z1; lia).
  assert (Hc4 : Qlt 0 (Z.of_nat (3 * n + 2 * m + 4) # 1)%Q) by (apply rx_Qlt_Z1; lia).
  assert (Hcd : Qlt 0 ((Z.of_nat (3 * n + 2 * m + 3) # 1)
                         * (Z.of_nat (3 * n + 2 * m + 4) # 1))%Q)
    by (apply Qmult_lt_0_compat; assumption).
  assert (HcdJp : cd * Jp == 1%Q).
  { unfold cd, Jp.
    rewrite <- (bk_Qmul_nat (3 * n + 2 * m + 3) (3 * n + 2 * m + 4)).
    unfold Qdiv. rewrite !Qmult_1_l. rewrite <- Qinv_mult_distr.
    apply Qmult_inv_r. apply lnt_qneq_of_eq0. exact Hcd. }
  assert (Ez1 : (Z.of_nat (Datatypes.S m * ((3 * n + 2 * m + 3) * (3 * n + 2 * m + 4))) # 1)%Q
              == ((Z.of_nat (Datatypes.S m) # 1) * cd)%Q)
    by (symmetry; apply bk_Qmul_nat).
  assert (Ez2 : (Z.of_nat ((n + m + 1) * ((n + 2 * m + 1) * (n + 2 * m + 2))) # 1)%Q
              == ((Z.of_nat (n + m + 1) # 1)
                    * (Z.of_nat ((n + 2 * m + 1) * (n + 2 * m + 2)) # 1))%Q)
    by (symmetry; apply bk_Qmul_nat).
  assert (Eab : (Z.of_nat ((n + 2 * m + 1) * (n + 2 * m + 2)) # 1)%Q
              == ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1))%Q)
    by (symmetry; apply bk_Qmul_nat).
  rewrite Ez1, Ez2, Eab.
  assert (HJpcd : Jp * cd == 1%Q) by (rewrite Qmult_comm; exact HcdJp).
  transitivity (((C1 * (Z.of_nat (Datatypes.S m) # 1))%Q
                  * ((Z.of_nat (n + 2 * m + 1) # 1) * (Z.of_nat (n + 2 * m + 2) # 1))%Q
                  * (Jp * cd)%Q * CF)%Q).
  - ring.
  - rewrite HJpcd.
    assert (Hsm : n + Datatypes.S m = n + m + 1) by lia.
    assert (Hkey : (C1 * (Z.of_nat (Datatypes.S m) # 1))%Q
                 == (C0 * (Z.of_nat (n + m + 1) # 1))%Q).
    { assert (Hnat := lnt_bkC_step n m). rewrite Hsm in Hnat.
      transitivity (Z.of_nat (bkC (Datatypes.S (n + m)) n * Datatypes.S m) # 1)%Q.
      - apply (bk_Qmul_nat (bkC (Datatypes.S (n + m)) n) (Datatypes.S m)).
      - transitivity (Z.of_nat (bkC (n + m) n * (n + m + 1)) # 1)%Q.
        + rewrite Hnat. reflexivity.
        + symmetry.
          apply (bk_Qmul_nat (bkC (n + m) n) (n + m + 1)). }
    rewrite Hkey. ring.
Qed.

(** 机器反例判定①：n=0,m=30 处 β 级数比率 R=1891/2016≈0.938 > 3/4
    ——「峰后一致比率 ρ=3/4」在 β 级数上被机器证伪。 *)
Theorem lnt_beta_rho_refuted34 : QltT ((3 # 4)%Q * bv_term 0 30)%Q (bv_term 0 31).
Proof. vm_compute. reflexivity. Qed.

(** 机器反例判定②：同点 R > 15/16——任何固定 ρ<1 的一致比率档在 β 级数
    上不存在（初版草案的 ρ^M 档不成立，改用极点级数尾对象）。 *)
Theorem lnt_beta_rho_refuted1516 : QltT ((15 # 16)%Q * bv_term 0 30)%Q (bv_term 0 31).
Proof. vm_compute. reflexivity. Qed.

(** 极点级数正例判定：n=2 窗内比率档 ≤ 3/4（机器复核）。 *)
Theorem lnt_pterm_anchor2 : QleT' (lnt_pterm 2 3) ((3 # 4)%Q * lnt_pterm 2 2).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §D 假设审计与独立提取（构造性验证位）                      *)
(* ============================================================ *)

Print Assumptions lnt_deficit_pos.
Print Assumptions lnt_bkC_le_pow2.
Print Assumptions lnt_pterm_pos.
Print Assumptions lnt_pterm_ratio.
Print Assumptions lnt_pterm_pow.
Print Assumptions lnt_geo_partial.
Print Assumptions lnt_pterm_tail.
Print Assumptions lnt_pterm_gap.
Print Assumptions lnt_pterm_peak.
Print Assumptions lnt_gap_geo.
Print Assumptions lnt_bv_cross.
Print Assumptions lnt_beta_rho_refuted34.
Print Assumptions lnt_beta_rho_refuted1516.
Print Assumptions lnt_pterm_anchor2.

From Stdlib Require Import Extraction.
Separate Extraction lnt_pterm_gap lnt_gap_geo lnt_pterm_peak lnt_bv_cross
  lnt_deficit_pos lnt_beta_rho_refuted34 lnt_beta_rho_refuted1516
  lnt_pterm_anchor2.
