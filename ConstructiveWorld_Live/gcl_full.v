(* ===================================================================== *)
(*  gcl_full.v —— DM-519B【μ_lib 8.64 全额入账收束件】：weld3 残前提三消          *)
(*  模块名：gcl_full。                                                     *)
(*  使命：承 GCL5R＋HENT 冻结遗产（gcl_supply_sym_weld3 前提三={m≥3·Hanson 熵· *)
(*        ④族界}·gcl_binom_bound born·gcl_hanson_win born），铸【全额版        *)
(*        供给链装配主件】gcl_supply_sym_weld3_full：                          *)
(*          · 前提 m≥3：由窗界 3≤m 逐字蕴含（零消解需求·weld3 槽前提兼为       *)
(*            assembly 槽前提）；                                            *)
(*          · 前提 Hanson 熵：gcl_hanson_win 窗内消去（HENT 件零改动使用）；    *)
(*          · 前提 ④族界：本件全额消去——滤波单调链（altsum 单调·GCL4 蓝图      *)
(*            「随梯机免费」兑现）⟹ I ≤ D_0 ＋ u 衰减（k ≤ m+3 逐点比率       *)
(*            (m+2+k)/(2m+4+k) ≤ 2/3）⟹ D_0 ≤ u(m,0)²·ΣC(m+1+k,m+1)(4/9)^k   *)
(*            ≤ u(m,0)²·(9/5)^(m+2)（gcl_binom_bound 零改动使用）            *)
(*            ＋单项式窗点判据 u(m,0)²·(9/5)^(m+2) ≤ (1/4)(1/12)^m（m∈[3,8]）。 *)
(*        数学负载（对照 _mirror_gcl5b_out.txt 16/16 全 PASS 在卷）：          *)
(*          · altsum 单调链：gcl_altsum_pascal ＋ CM(f∘S)≥0（dfa_shiftfun）    *)
(*            ⟹ altsum f (S n) ≤ altsum f 0——Isum^sym ≤ D_0 对一切 M 成立；   *)
(*          · u 衰减：gcl_u_shift 乘法形＋Qle 右乘消元 ⟹ u(m,k) ≤ (2/3)^k·u(m,0) *)
(*            （k ≤ m+3）；k>m+3 衰减界失效（对照 S10 检查点）＝anchor M:=m       *)
(*            的定理边界；                                                   *)
(*          · 单项式窗点：比值 0.329→0.7196 递升、m=9 仍真（0.8795）、m=10 破   *)
(*            （对照 S7b）——窗 [3,8] 由 Hanson 熵侧先行锁定（真墙档）。        *)
(*  诚实边界（fail-loud）：                                                  *)
(*    - 全称 m（窗 [3,8] 之外）＝Hanson 熵真墙侧（HENT 三档归档＋四复审条件）， *)
(*      本件零越权；[3,8]∪[9,∞) 分段式的第二段候熵段扩窗（窗右界扩展）。       *)
(*    - 全称 M＝本链只覆盖 M ≤ m+3；锚版 M:=m 已覆盖。全称 M 需超几何收敛      *)
(*      闭式和（对照 S10：真 D_0 收敛远小于每-k 界·闭式求和另案）。            *)
(*    - gcl_supply_sym_weld3（GCL5R 冻结件）签名零触碰——本件只加 full 版       *)
(*      （律六签名稳定）。                                                   *)
(*  构造性（红线四要素·逐件）：                                              *)
(*    - 纯构造性：全件 Qed/Defined，零 Axiom／零 Parameter／零 Admitted／零承认式收尾／零经典；   *)
(*    - Set 层：主语句 gcl_supply_sym_weld3_full 值域 gcl_supply_sym（sigT·Set） *)
(*      承载；各辅助件 QleT'（Set）或 Qeq/Qle 推理脚手架（池先例）；           *)
(*    - 非平凡：单调链归纳＋u 衰减逐点比率归纳＋五肢焊接，非占位；             *)
(*    - 可提取：Separate Extraction 主语句；文末 Print Assumptions。            *)
(*  依赖：Stdlib；S01/S02/S03/BeukersLists/PolyIntegral/PintMono；ζ2 池       *)
(*        abl_z2_truncfam/abl_z2_itg_carrier；HansonLcm＋Hanson3Pow；         *)
(*        GCL 冻结四件（coefficient/famsym/isumsym/cert）；HENT born 件        *)
(*        gcl_hent（md5 8d76cd37 池内播种·与 HENT 池逐位同）。                 *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && cd 本池 && cpu_guard v3 默认档包裹 rocq c        *)
(*        -native-compiler no -q -Q _world "" gcl_full.v（并发=1 单飞）。      *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia Setoid.
From Stdlib Require Import Lists.List.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PintMono.
Require Import abl_z2_truncfam abl_z2_itg_carrier HansonLcm Hanson3Pow.
Require Import gcl_coefficient gcl_famsym gcl_isumsym gcl_cert gcl_hent.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* §0 小件舱                                                                  *)
(* ============================================================ *)

(* 逐点不等 ⟹ 和不等（jsum 单调·qleT'_plus_compat 收束） *)
Lemma gcl_jsum_mono : forall (f g : nat -> Q) (n : nat),
  (forall j : nat, (j <= n)%nat -> QleT' (f j) (g j)) ->
  QleT' (gcl_jsum f n) (gcl_jsum g n).
Proof.
  intros f g n. induction n as [| n IH]; intros H.
  - cbn [gcl_jsum]. apply H. lia.
  - cbn [gcl_jsum].
    apply (qleT'_plus_compat (gcl_jsum f n) (gcl_jsum g n)
             (f (Datatypes.S n)) (g (Datatypes.S n))).
    + apply IH. intros j Hj. apply H. lia.
    + apply H. lia.
Qed.

(* 减非负不增：A − B ≤ A（B ≥ 0）——变元 A 不可与 A+0 转换（gcl_le1_sub 字面形
   1+0 可算而变元形卡壳·首发红校正），Qle_trans 过 A+0＋Qplus_0_r 桥收束 *)
Lemma gcl_sub_ge0_le : forall A B : Q, QleT' 0 B -> QleT' (A - B) A.
Proof.
  intros A B HB. apply Qle_to_QleT'.
  apply (Qle_trans (A - B) (A + Qopp B) A).
  - unfold Qminus. apply Qle_refl.
  - apply (Qle_trans (A + Qopp B) (A + 0) A).
    + apply (Qplus_le_compat A A (Qopp B) 0).
      * apply Qle_refl.
      * apply (Qle_trans _ (Qopp 0)).
        -- apply Qopp_le_compat. apply QleT'_to_Qle. exact HB.
        -- apply Qle_refl.
    + apply qeq_imp_qle. apply Qplus_0_r.
Qed.

(* 幂积：(x)^k·(y)^k == (x·y)^k（q_pow_succ 归纳·免 Qdiv） *)
Lemma gcl_qpow_mul2 : forall (k : nat) (x y : Q),
  q_pow x k * q_pow y k == q_pow (x * y) k.
Proof.
  intro k. induction k as [| k IH]; intros x y.
  - reflexivity.
  - rewrite (q_pow_succ x k), (q_pow_succ y k), (q_pow_succ (x * y) k).
    rewrite <- (IH x y). ring.
Qed.

(* bkC 对称：C(n,k) = C(n,n−k)（k ≤ n·Pascal 双叶归纳） *)
Lemma gcl_bkC_sym : forall n k : nat, (k <= n)%nat -> bkC n k = bkC n (n - k)%nat.
Proof.
  intro n. induction n as [| n IH]; intros k Hk.
  - destruct k as [| k'].
    + reflexivity.
    + lia.
  - destruct k as [| k'].
    + rewrite gcl_bkC_zero.
      replace (Datatypes.S n - 0)%nat with (Datatypes.S n)%nat by lia.
      rewrite (bkC_diag (Datatypes.S n)). reflexivity.
    + assert (Hk' : (k' <= n)%nat) by lia.
      rewrite gcl_pascal1.
      destruct (Nat.eq_dec k' n) as [Heq | Hne].
      * subst k'.
        rewrite (bkC_out n (Datatypes.S n)) by lia.
        rewrite (bkC_diag n).
        replace (Datatypes.S n - Datatypes.S n)%nat with 0%nat by lia.
        rewrite gcl_bkC_zero. reflexivity.
      * assert (Hlt : (Datatypes.S k' <= n)%nat) by lia.
        assert (E1 : bkC n k' = bkC n (n - k')%nat) by (apply IH; lia).
        assert (E2 : bkC n (Datatypes.S k') = bkC n (n - Datatypes.S k')%nat)
          by (apply IH; lia).
        rewrite E1, E2.
        replace (Datatypes.S n - Datatypes.S k')%nat
          with (Datatypes.S (n - Datatypes.S k'))%nat by lia.
        rewrite gcl_pascal1.
        replace (Datatypes.S (n - Datatypes.S k'))%nat with (n - k')%nat by lia.
        rewrite <- E1.
        lia.
Qed.

(* ============================================================ *)
(* §1 ④肢半程主语句：滤波单调链 altsum f (S n) ≤ altsum f 0                            *)
(*    （GCL4 蓝图「随梯机免费」兑现：pascal ＋ CM(f∘S)·dfa_shiftfun）                 *)
(* ============================================================ *)

Lemma gcl_altsum_0 : forall f : nat -> Q, gcl_altsum f 0%nat == f 0%nat.
Proof.
  intro f. unfold gcl_altsum. cbn [gcl_jsum gcl_sgn].
  rewrite bkC_diag, gcl_oneQ. ring.
Qed.

(* CM(f) ⟹ 移位滤波 altsum(f∘S) ≥ 0（dfa_shiftfun 换形＋HCM 逐点） *)
Lemma gcl_altsum_shift_ge0 : forall (n : nat) (f : nat -> Q),
  (forall i j : nat, QleT' 0 (gcl_dfa i f j)) ->
  QleT' 0 (gcl_altsum (fun j => f (Datatypes.S j)) n).
Proof.
  intros n f HCM. apply gcl_altsum_cm. intros i j Hij.
  apply (gcl_qle_wd_r (gcl_dfa i f (Datatypes.S j))).
  - exact (Qeq_sym _ _ (gcl_dfa_shiftfun i f j)).
  - apply HCM.
Qed.

(* 滤波单调链：CM(f) ⟹ altsum f (S n) ≤ altsum f 0（pascal 逐步减移位滤波） *)
Lemma gcl_altsum_dec : forall (n : nat) (f : nat -> Q),
  (forall i j : nat, QleT' 0 (gcl_dfa i f j)) ->
  QleT' (gcl_altsum f (Datatypes.S n)) (gcl_altsum f 0%nat).
Proof.
  intro n. induction n as [| n IH]; intros f HCM.
  - apply (gcl_qle_wd_l (gcl_altsum f (Datatypes.S 0%nat))
             (gcl_altsum f 0%nat - gcl_altsum (fun j => f (Datatypes.S j)) 0%nat)
             (gcl_altsum f 0%nat)).
    + apply gcl_altsum_pascal.
    + apply gcl_sub_ge0_le. apply (gcl_altsum_shift_ge0 0%nat f HCM).
  - apply (gcl_qleT_trans (gcl_altsum f (Datatypes.S (Datatypes.S n)))
             (gcl_altsum f (Datatypes.S n)) (gcl_altsum f 0%nat)).
    + apply (gcl_qle_wd_l (gcl_altsum f (Datatypes.S (Datatypes.S n)))
               (gcl_altsum f (Datatypes.S n)
                - gcl_altsum (fun j => f (Datatypes.S j)) (Datatypes.S n))
               (gcl_altsum f (Datatypes.S n))).
      * apply gcl_altsum_pascal.
      * apply gcl_sub_ge0_le.
        apply (gcl_altsum_shift_ge0 (Datatypes.S n) f HCM).
    + apply IH. exact HCM.
Qed.

(* 主语句【④肢半程】：Isum^sym ≤ D_0（对一切 m·M 成立·零前提） *)
Theorem gcl_Isum_sym_le_D0 : forall m M : nat,
  QleT' (gcl_Isum_sym m M) (gcl_isum_kl 1 m 0%nat M).
Proof.
  intros m M.
  apply (gcl_qle_wd_l (gcl_Isum_sym m M) (gcl_isym_closed m M)
           (gcl_isum_kl 1 m 0%nat M)).
  - exact (gcl_Isum_sym_closed m M).
  - apply (gcl_qle_wd_l (gcl_isym_closed m M)
             (gcl_altsum (fun j => gcl_isum_kl 1 m j M)
                         (Datatypes.S (Datatypes.S m)))
             (gcl_isum_kl 1 m 0%nat M)).
    + unfold gcl_isym_closed, gcl_altsum. reflexivity.
    + apply (gcl_qleT_trans
               (gcl_altsum (fun j => gcl_isum_kl 1 m j M)
                           (Datatypes.S (Datatypes.S m)))
               (gcl_altsum (fun j => gcl_isum_kl 1 m j M) 0%nat)
               (gcl_isum_kl 1 m 0%nat M)).
      * apply gcl_altsum_dec. intros i j. apply gcl_D_cm.
      * apply (gcl_qle_wd_l
                 (gcl_altsum (fun j => gcl_isum_kl 1 m j M) 0%nat)
                 ((fun j => gcl_isum_kl 1 m j M) 0%nat)
                 (gcl_isum_kl 1 m 0%nat M)).
        -- apply gcl_altsum_0.
        -- apply Qle_to_QleT'. apply Qle_refl.
Qed.

(* ============================================================ *)
(* §2 u 衰减面：u(m,k) ≤ (2/3)^k·u(m,0)（k ≤ m+3·乘 D 消元·免 Qdiv/Qinv）             *)
(*    （二红校正：stdlib Qinv 对 Z.of_nat 分母不约简＋# 记法第二参须 positive         *)
(*      ——Qinv 系三引理撤除，改走 Qle 右乘消元＋纯 natQ 线性比率判据）                 *)
(* ============================================================ *)

(* Qle 右乘消元（0 < a）：a·x ≤ a·y ⟹ x ≤ y（Qlt_le_dec 分案＋stdlib 名装配） *)
Lemma gcl_le_mul_cancel_r : forall a x y : Q, Qlt 0 a -> (a * x <= a * y)%Q -> (x <= y)%Q.
Proof.
  intros a x y Ha H.
  destruct (Qlt_le_dec x y) as [Hxy | Hyx].
  - apply Qlt_le_weak. exact Hxy.
  - destruct (Qeq_dec x y) as [Heq | Hne].
    + apply qeq_imp_qle. exact Heq.
    + exfalso.
      assert (Hlt : (y < x)%Q).
      { destruct (Qlt_le_dec y x) as [Hlt2|Hle2].
        - exact Hlt2.
        - exfalso. apply Hne. apply Qle_antisym; [exact Hle2 | exact Hyx]. }
      pose proof (Qmult_lt_compat_r y x a Ha Hlt) as H3.
      pose proof (proj1 (Qle_comp (a * x) (x * a) (Qmult_comm a x)
                                  (a * y) (y * a) (Qmult_comm a y)) H) as H4.
      exact (Qlt_not_le (y * a) (x * a) H3 H4).
Qed.

(* 幂正性：0 < x ⟹ 0 < x^k（gcl_mult_pos 归纳） *)
Lemma gcl_qpow_pos : forall (x : Q) (k : nat), Qlt 0 x -> Qlt 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - unfold Qlt. cbn [q_pow Qnum Qden]. lia.
  - rewrite (q_pow_succ x k). apply gcl_mult_pos; assumption.
Qed.

(* 线性比率（乘法形）：m+2+k ≤ (2/3)·(2m+4+k)（k ≤ m+2·纯 natQ 线性判据·免 Qdiv） *)
Lemma gcl_u_ratio_lin : forall m k : nat, (k <= m + 2)%nat ->
  QleT' ((Z.of_nat (m + 2 + k) # 1)%Q) ((2#3) * (Z.of_nat (2 * m + 4 + k) # 1)%Q).
Proof.
  intros m k H. apply Qle_to_QleT'.
  unfold Qle. cbn [Qnum Qden Qmult]. lia.
Qed.

(* u 衰减：k ≤ m+3 ⟹ u(m,k) ≤ (2/3)^k·u(m,0)
   （u_shift 乘法形 ＋ IH 左乘 N ＋ 线性比率左乘 ＋ q_pow_succ 换形 ＋ 乘 D 右乘消元） *)
Lemma gcl_u_decay : forall m k : nat, (k <= m + 3)%nat ->
  QleT' (gcl_u m k) (q_pow (2#3) k * gcl_u m 0%nat).
Proof.
  intros m k. induction k as [| k IH]; intros Hk.
  - apply gcl_qleT_of_eq. cbn [q_pow]. ring.
  - assert (Hk2 : (k <= m + 2)%nat) by lia.
    assert (HD : Qlt 0 (Z.of_nat (2 * m + 4 + k) # 1)) by (apply gcl_natQ_lt; lia).
    assert (Hmul : QleT' (gcl_u m (Datatypes.S k) * (Z.of_nat (2 * m + 4 + k) # 1))
                         (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat
                          * (Z.of_nat (2 * m + 4 + k) # 1))).
    { apply (gcl_qle_wd_l
               (gcl_u m (Datatypes.S k) * (Z.of_nat (2 * m + 4 + k) # 1))
               (gcl_u m k * (Z.of_nat (m + 2 + k) # 1))
               (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat
                * (Z.of_nat (2 * m + 4 + k) # 1))).
      - exact (gcl_u_shift m k).
      - apply (gcl_qle_wd_r
                 ((q_pow (2#3) k * gcl_u m 0%nat)
                  * ((2#3) * (Z.of_nat (2 * m + 4 + k) # 1)))).
        + rewrite (q_pow_succ (2#3) k). ring.
        + apply (gcl_qleT_trans
                   (gcl_u m k * (Z.of_nat (m + 2 + k) # 1))
                   ((q_pow (2#3) k * gcl_u m 0%nat) * (Z.of_nat (m + 2 + k) # 1))
                   ((q_pow (2#3) k * gcl_u m 0%nat)
                    * ((2#3) * (Z.of_nat (2 * m + 4 + k) # 1)))).
          * apply Qle_to_QleT'.
            apply (gcl_qle_mul_compat (gcl_u m k) (q_pow (2#3) k * gcl_u m 0%nat)
                     (Z.of_nat (m + 2 + k) # 1)).
            -- apply IH. lia.
            -- apply Qlt_le_weak. apply gcl_natQ_lt. lia.
          * apply Qle_to_QleT'.
            apply (gcl_qle_mul_compat_l (Z.of_nat (m + 2 + k) # 1)
                     ((2#3) * (Z.of_nat (2 * m + 4 + k) # 1))
                     (q_pow (2#3) k * gcl_u m 0%nat)).
            -- apply gcl_u_ratio_lin. exact Hk2.
            -- apply Qmult_le_0_compat.
               ++ apply Qlt_le_weak. apply gcl_qpow_pos.
                  unfold Qlt. cbn [Qnum Qden]. lia.
               ++ apply Qlt_le_weak. apply gcl_u_pos. }
    apply Qle_to_QleT'.
    apply (gcl_le_mul_cancel_r (Z.of_nat (2 * m + 4 + k) # 1)
             (gcl_u m (Datatypes.S k))
             (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat)).
    + exact HD.
    + assert (HP : (Z.of_nat (2 * m + 4 + k) # 1) * gcl_u m (Datatypes.S k)
                   <= (Z.of_nat (2 * m + 4 + k) # 1)
                      * (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat)%Q).
      { apply (proj1 (Qle_comp
               (gcl_u m (Datatypes.S k) * (Z.of_nat (2 * m + 4 + k) # 1))
               ((Z.of_nat (2 * m + 4 + k) # 1) * gcl_u m (Datatypes.S k))
               (Qmult_comm (gcl_u m (Datatypes.S k)) (Z.of_nat (2 * m + 4 + k) # 1))
               (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat * (Z.of_nat (2 * m + 4 + k) # 1))
               ((Z.of_nat (2 * m + 4 + k) # 1) * (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat))
               (Qmult_comm (q_pow (2#3) (Datatypes.S k) * gcl_u m 0%nat)
                           (Z.of_nat (2 * m + 4 + k) # 1)))).
        apply QleT'_to_Qle. exact Hmul. }
      exact HP.
Qed.

(* u² 衰减：k ≤ m+3 ⟹ u(m,k)² ≤ (4/9)^k·u(m,0)² *)
Lemma gcl_u_sq_decay : forall m k : nat, (k <= m + 3)%nat ->
  QleT' (gcl_u m k * gcl_u m k)
        (q_pow (4#9) k * (gcl_u m 0%nat * gcl_u m 0%nat)).
Proof.
  intros m k Hk. pose proof (gcl_u_decay m k Hk) as Hd.
  apply (gcl_qle_wd_r
           ((q_pow (2#3) k * gcl_u m 0%nat) * (q_pow (2#3) k * gcl_u m 0%nat))).
  - assert (Hq : q_pow (2#3) k * q_pow (2#3) k == q_pow (4#9) k).
    { transitivity (q_pow ((2#3) * (2#3)) k).
      - apply gcl_qpow_mul2.
      - apply q_pow_wd. reflexivity. }
    transitivity ((q_pow (2#3) k * q_pow (2#3) k)
                  * (gcl_u m 0%nat * gcl_u m 0%nat)).
    + ring.
    + rewrite Hq. ring.
  - apply Qle_to_QleT'.
    apply (Qle_trans (gcl_u m k * gcl_u m k)
                     (q_pow (2#3) k * gcl_u m 0%nat * gcl_u m k)
                     (q_pow (2#3) k * gcl_u m 0%nat * (q_pow (2#3) k * gcl_u m 0%nat))).
    + apply (Qmult_le_compat_r (gcl_u m k) (q_pow (2#3) k * gcl_u m 0%nat)
               (gcl_u m k)).
      * apply QleT'_to_Qle. exact Hd.
      * apply Qlt_le_weak. apply gcl_u_pos.
    + apply (gcl_qle_mul_compat_l (gcl_u m k) (q_pow (2#3) k * gcl_u m 0%nat)
               (q_pow (2#3) k * gcl_u m 0%nat)).
      * exact Hd.
      * apply Qmult_le_0_compat.
        -- apply Qlt_le_weak. apply gcl_qpow_pos.
           unfold Qlt. cbn [q_pow Qnum Qden]. lia.
        -- apply Qlt_le_weak. apply gcl_u_pos.
Qed.

(* ============================================================ *)
(* §3 D_0 界：D_0 ≤ u(m,0)²·Σ_{k≤M} C(m+1+k,m+1)(4/9)^k（M ≤ m+3）               *)
(* ============================================================ *)

Theorem gcl_D0_le_bins : forall m M : nat, (M <= m + 3)%nat ->
  QleT' (gcl_isum_kl 1 m 0%nat M)
        (gcl_u m 0%nat * gcl_u m 0%nat
         * gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                              * q_pow (4#9) k) M).
Proof.
  intros m M HM.
  apply (gcl_qle_wd_l (gcl_isum_kl 1 m 0%nat M)
           (gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                               * (gcl_u m (0 + k)%nat * gcl_u m (0 + k)%nat)) M)
           (gcl_u m 0%nat * gcl_u m 0%nat
            * gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                                 * q_pow (4#9) k) M)).
  - exact (gcl_isum_kl_jsum m M 0%nat).
  - apply (gcl_qle_wd_r (gcl_jsum (fun k => gcl_u m 0%nat * gcl_u m 0%nat
                                             * ((Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                                                * q_pow (4#9) k)) M)).
    + apply gcl_jsum_scale.
    + apply gcl_jsum_mono. intros k Hk.
      apply (gcl_qle_wd_l
               ((Z.of_nat (bkC (Datatypes.S m + k) (Datatypes.S m)) # 1)
                * (gcl_u m (0 + k)%nat * gcl_u m (0 + k)%nat))
               ((Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                * (gcl_u m k * gcl_u m k))
               (gcl_u m 0%nat * gcl_u m 0%nat
                * ((Z.of_nat (bkC (Datatypes.S m + k) k) # 1) * q_pow (4#9) k))).
      * rewrite (gcl_bkC_sym (Datatypes.S m + k)%nat (Datatypes.S m)) by lia.
        replace (Datatypes.S m + k - Datatypes.S m)%nat with k%nat by lia.
        reflexivity.
      * apply (gcl_qle_wd_r
                 ((Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                  * (q_pow (4#9) k * (gcl_u m 0%nat * gcl_u m 0%nat)))
                 (gcl_u m 0%nat * gcl_u m 0%nat
                  * ((Z.of_nat (bkC (Datatypes.S m + k) k) # 1) * q_pow (4#9) k))).
        -- ring.
        -- apply Qle_to_QleT'.
           apply (gcl_qle_mul_compat_l (gcl_u m k * gcl_u m k)
                     (q_pow (4#9) k * (gcl_u m 0%nat * gcl_u m 0%nat))
                     ((Z.of_nat (bkC (Datatypes.S m + k) k) # 1))).
           ++ apply gcl_u_sq_decay. lia.
           ++ apply QleT'_to_Qle. apply gcl_natQ_ge0_all.
Qed.

(* 单项式窗点：m∈[3,8] ⟹ u(m,0)²·(9/5)^(m+2) ≤ (1/4)(1/12)^m
   （六叶 destruct＋lia 剪枝＋vm_compute 字面判据——对照 S7 逐档比值
     0.329/0.367/0.422/0.497/0.594/0.720·m=9 仍真 0.879·m=10 破） *)
Lemma gcl_u0_weight_win : forall m : nat, (3 <= m)%nat -> (m <= 8)%nat ->
  QleT' (gcl_u m 0%nat * gcl_u m 0%nat
         * q_pow (9#5) (Datatypes.S (Datatypes.S m)))
        (gcl_weight_G m).
Proof.
  intros m H3 H8.
  destruct m as [|[|[|[|[|[|[|[|[|g]]]]]]]]]; try lia.
  all: vm_compute; reflexivity.
Qed.

(* ============================================================ *)
(* §4 主语句【全额版供给链装配主件】：窗界唯一前提·weld3 三前提全消                     *)
(* ============================================================ *)

(* 前提 m≥3：窗界 3≤m 逐字蕴含（零消解需求）；Hanson 熵：gcl_hanson_win 窗内消去；
   ④族界：I ≤ D_0（§1）＋ D_0 ≤ u0²·bins（§3）＋ binom_bound（GCL5R born）
   ＋单项式窗点（§3）四段全额消去——供给链五肢零残位。 *)
Theorem gcl_supply_sym_weld3_full : forall m : nat,
  (3 <= m)%nat -> (m <= 8)%nat -> gcl_supply_sym m m.
Proof.
  intros m H3 H8.
  apply (gcl_supply_sym_weld3 m m H3 (gcl_hanson_win m H3 H8)).
  apply (gcl_qleT_trans (gcl_Isum_sym m m)
           (gcl_u m 0%nat * gcl_u m 0%nat
            * q_pow (9#5) (Datatypes.S (Datatypes.S m)))
           (gcl_weight_G m)).
  - apply (gcl_qleT_trans (gcl_Isum_sym m m) (gcl_isum_kl 1 m 0%nat m)
             (gcl_u m 0%nat * gcl_u m 0%nat
              * q_pow (9#5) (Datatypes.S (Datatypes.S m)))).
    + apply gcl_Isum_sym_le_D0.
    + apply (gcl_qleT_trans (gcl_isum_kl 1 m 0%nat m)
               (gcl_u m 0%nat * gcl_u m 0%nat
                * gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                                     * q_pow (4#9) k) m)
               (gcl_u m 0%nat * gcl_u m 0%nat
                * q_pow (9#5) (Datatypes.S (Datatypes.S m)))).
      * apply gcl_D0_le_bins. lia.
      * apply Qle_to_QleT'.
        apply (gcl_qle_mul_compat_l
                 (gcl_jsum (fun k => (Z.of_nat (bkC (Datatypes.S m + k) k) # 1)
                                      * q_pow (4#9) k) m)
                 (q_pow (9#5) (Datatypes.S (Datatypes.S m)))
                 (gcl_u m 0%nat * gcl_u m 0%nat)).
        -- apply gcl_binom_bound.
        -- apply Qmult_le_0_compat; apply Qlt_le_weak; apply gcl_u_pos.
  - apply gcl_u0_weight_win.
    + exact H3.
    + exact H8.
Defined.

(* ============================================================ *)
(* §5 提取与假设审计                                                              *)
(* ============================================================ *)

Print Assumptions gcl_Isum_sym_le_D0.
Print Assumptions gcl_altsum_dec.
Print Assumptions gcl_u_decay.
Print Assumptions gcl_D0_le_bins.
Print Assumptions gcl_u0_weight_win.
Print Assumptions gcl_supply_sym_weld3_full.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log".
Separate Extraction gcl_supply_sym_weld3_full.
