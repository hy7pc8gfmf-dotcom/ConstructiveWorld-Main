(* ============================================================ *)
(* BeukersVariant.v —— 切片代理I（批次 E-STAGING-D021，20260918）      *)
(* P2 第二攻切片：(1+t)^{n+1} 变体恒等式构造（bv_ 前缀）。              *)
(*                                                                 *)
(* 【定形数值锚（本席手算 n=0,1,2,3，先锚后施工——D016 教训）】          *)
(* 变体积分 I'_n := ∫₀¹ tⁿ(1−t)ⁿ/(1+t)^{n+1} dt。换元 u = 1+t 后        *)
(* 被积函数为 Laurent 型，逐点：                                       *)
(*   n=0: I'_0 = ∫₀¹ dt/(1+t) = ln2；q̃_0 = 1，p_0 = 0；                 *)
(*         ln2 − 0/1 == ln2 == I'_0/1。 ✓                              *)
(*   n=1: (u−1)(2−u)/u² = −1 + 3/u − 2/u² ⟹ I'_1 = 3ln2 − 2；           *)
(*         q̃_1 = 3，p_1 = 2；ln2 − 2/3 == (3ln2−2)/3 == I'_1/3。 ✓      *)
(* 【定形主结论：真归一形为 ln2 − p_n/q̃_n == I'_n/q̃_n（无 2 幂）】       *)
(* 任务书草案 x''_n := p_n/(2^n·q̃_n) 与差式 I'_n/(2^n·q̃_n) 联立强迫      *)
(* (2^n − 1)·ln2 == 0（n≥1 假）——2 幂归一死亡；Q 层正分离见证           *)
(* bv_x2pow_sep1（x''_1 = 2/(2·3) = 1/3 < 2/3 = x_1）。                  *)
(* 【p_n 序列勘定：谐和形不配，Laurent 反推闭式】                        *)
(*   p_n = −Σ_{j=0, j≠n}^{2n} c_j·(2^{j−n} − 1)/(j−n)，                 *)
(*   c_j = [u^j](u−1)ⁿ(2−u)ⁿ = (−1)^{n+j}·Σ_a C(n,a)C(n,j−a)2^{n−(j−a)}；*)
(* ln2 系数 c_n == Σ_a C(n,a)²·2^a == D_n（Delannoy）== q̃_n（离散核）。  *)
(* p 序列：0, 2, 9, 131/3（n=3 起非整——有理分子族，与 D016               *)
(* "P*_2(1/2)=4.5 非整"同族印证）；谐和 P_n(1) = 0, 1, 11/2 不配。       *)
(* 跨变体核对：r_n == 2^{n+1}·p_n（D016 r: 0, 8, 72 全吻合）。           *)
(* 【级数定形（全正项）】1/(1+t)^{n+1} = (1−t)^{n+1}/(1−t²)^{n+1}        *)
(*   = Σ_{m≥0} C(n+m,n)·t^{2m}·(1−t)^{n+1}，故                          *)
(*   I'_n = Σ_{m≥0} C(n+m,n)·B(n+2m+1, 2n+1)（Beta 全正）。截断承载      *)
(*   bv_carrier n M 逐点 == tⁿ(1−t)^{2n+1}·Σ_{m≤M}C(n+m,n)t^{2m}，       *)
(*   积分 == 级数部分和（bv_carrier_value，精确 QeqT）。                 *)
(*                                                                 *)
(* 【本席交付面（七主件，全 Qed 零承认）】                               *)
(*  ① bv_delannoy_eq_qtilde：升幂 Delannoy 和 Σ_{a≤n}C(n,a)²2^a == q̃_n   *)
(*     （ln2 系数离散核；bk_psd_ext + bk_Qn_sym 镜像归位）。             *)
(*  ② bv_term_pos：级数项 C(n+m,n)·B(n+2m+1,2n+1) 严格正（QltT 面）。    *)
(*  ③ bv_carrier_eval：截断承载逐点语义（pei_list 配方，tⁿ(1−t)^{2n+1}   *)
(*     × 负二项截断）。                                                 *)
(*  ④ bv_carrier_value：截断积分 == 级数部分和（精确 QeqT——本切片       *)
(*     最重件）。                                                       *)
(*  ⑤ bv_sum_mono：截断积分单调链（QleT'——消费 PintMono 的               *)
(*     pm_scale_mono/pm_add_mono/pm_qle_wd_l/pm_qle_wd_r 线性单调面）。  *)
(*  ⑥ bv_sum_pos：部分和严格正（QltT——I'_n ≥ 部分和 > 0 的 Q 层承载）。  *)
(*  ⑦ bv_p 闭式定义 + 数值锚组（p: 0, 2, 9, 131/3；x: 0, 2/3, 9/13；     *)
(*     c_n: 3, 13, 63；2 幂死亡分离 bv_x2pow_sep1）。                   *)
(*                                                                 *)
(* 剩余路径卡点定位（P2 下席续接）：                                     *)
(*  (a) 恒等式本体 ln2 − p_n/q̃_n == I'_n/q̃_n 的语句化需实数层 ln2        *)
(*      （ln2 ∉ Q，Q 层不可语句化）——real 层装配另案（同 D016 (c)）；    *)
(*  (b) 部分和 → I'_n 的收敛桥需极限/逐点正机（P1b 残面）；              *)
(*  (c) 一般 n 的 bv_c n n == q̃_n：bk_psQ 升幂和 ↔ bk_psd 降幂和的       *)
(*      reindex 桥缺（bk_half_psd 只覆盖 (1/2)^k 降幂换基形）；          *)
(*  (d) 上界 I'_n ≤ B(n+1,n+1)：被积函数 monomial 基系数交错，            *)
(*      pm_pointwise_le 系数级面不适用（诚实登记）；逐点机另案。          *)
(*                                                                 *)
(* 红线自审：① 零承认面（全件 Qed，零承认词，依赖全在册）；             *)
(*   ② 语句面 Set（主件 QeqT/QltT/QleT'；Qeq/Qle/Qlt 支撑引理 Prop 面    *)
(*      仅作推理脚手架，D016/PadeErrorIntegral 先例同构）；              *)
(*   ③ 非平凡（Beta 级数定形 + 截断承载精确值 + 线性单调链消费 +         *)
(*      Laurent 符号和分子闭式）；                                       *)
(*   ④ 可提取（G3 探针独立文件实测，Obj.magic 计数=0）。                 *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp PolyIntegral           *)
(*   （alignb_base 信任缓存在册）+ UpReqB4TwoStage（alignb_base）        *)
(*   + PadeErrorIntegral BeukersLists PintMono（/tmp/e121_side 现编）。   *)
(* 零云端零 git。                                                       *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral.
Require Import PadeErrorIntegral BeukersLists PintMono.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 级数定形件：C(n+m,n)·B(n+2m+1, 2n+1)（全正项）                     *)
(* ============================================================ *)

Definition bv_term (n m : nat) : Q :=
  ((Z.of_nat (bkC (n + m) n) # 1) *
     (q_fact (n + 2 * m) * q_fact (2 * n + 1) / q_fact (3 * n + 2 * m + 2)))%Q.

(* 级数项 == C(n+m,n) × Beta 积分（pei 机的精确对接件） *)
Lemma bv_term_value : forall n m : nat,
  bv_term n m ==
  ((Z.of_nat (bkC (n + m) n) # 1) * pint_integral (pei_list (n + 2 * m) (2 * n + 1)))%Q.
Proof.
  intros n m. unfold bv_term.
  rewrite (pei_beta_value (n + 2 * m) (2 * n + 1)).
  replace ((n + 2 * m) + (2 * n + 1) + 1)%nat with (3 * n + 2 * m + 2)%nat by lia.
  reflexivity.
Qed.

(* 主件②：级数项严格正（bkC ≥ 1 × Beta 正） *)
Theorem bv_term_pos : forall n m : nat, QltT 0 (bv_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold bv_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - assert (Hb : 1 <= bkC (n + m) n) by (apply bkC_pos; lia).
    assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
    unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ============================================================ *)
(* §B 截断承载（pei_list/pei_eb_list 配方；步进垫双零）                   *)
(* ============================================================ *)

Definition bv_pad (p : list Q) : list Q := pei_ztail (pei_ztail p).

Lemma bv_pad_eval : forall (p : list Q) (x : Q),
  pint_eval (bv_pad p) x == pint_eval p x.
Proof.
  intros p x. unfold bv_pad.
  rewrite pei_eval_ztail, pei_eval_ztail. reflexivity.
Qed.

Lemma bv_pad_int : forall p : list Q,
  pint_integral (bv_pad p) == pint_integral p.
Proof.
  intro p. unfold bv_pad.
  rewrite pei_integral_ztail, pei_integral_ztail. reflexivity.
Qed.

Lemma bv_pad_length : forall p : list Q, length (bv_pad p) = (length p + 2)%nat.
Proof.
  intro p. unfold bv_pad, pei_ztail.
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

(* 承载：Σ_{m≤M} C(n+m,n)·list(t^{n+2m}(1−t)^{2n+1})（pei_eb_list 同构） *)
Fixpoint bv_carrier (n M : nat) : list Q :=
  match M with
  | 0 => pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                    (pei_list (n + 2 * 0) (2 * n + 1))
  | Datatypes.S m =>
      pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                           (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
               (bv_pad (bv_carrier n m))
  end.

Lemma bv_carrier_length : forall n M : nat,
  length (bv_carrier n M) = (3 * n + 2 * M + 2)%nat.
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    rewrite pei_scale_length, pei_list_length. lia.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { rewrite pei_scale_length, pei_list_length, bv_pad_length, IH. lia. }
    rewrite (pei_add_length _ _ HL).
    rewrite pei_scale_length, pei_list_length. lia.
Qed.

(* 主件③：逐点语义 == tⁿ(1−t)^{2n+1} × 负二项截断 Σ_{m≤M}C(n+m,n)(t²)^m *)
Theorem bv_carrier_eval : forall (n M : nat) (t : Q),
  pint_eval (bv_carrier n M) t ==
  q_pow t n * q_pow (1 - t)%Q (2 * n + 1) *
    bk_psQ (fun m : nat => (Z.of_nat (bkC (n + m) n) # 1)%Q)
           (Datatypes.S M) (t * t)%Q.
Proof.
  intros n M. induction M as [| m IH]; intro t.
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                   (Datatypes.S 0) (t * t)%Q)
      with (0 + (Z.of_nat (bkC (n + 0) n) # 1) * 1)%Q.
    rewrite pei_eval_scale, pei_beta_eval.
    replace (n + 2 * 0)%nat with n%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    rewrite pei_eval_add, pei_eval_scale, pei_beta_eval, bv_pad_eval, IH.
    assert (HpsQ : bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S (Datatypes.S m)) (t * t)%Q
                   == bk_psQ (fun m0 : nat => (Z.of_nat (bkC (n + m0) n) # 1)%Q)
                          (Datatypes.S m) (t * t)%Q
                      + (Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q
                          * q_pow (t * t)%Q (Datatypes.S m))
      by reflexivity.
    rewrite HpsQ.
    rewrite (q_pow_add t n (2 * Datatypes.S m)).
    replace (2 * Datatypes.S m)%nat with (Datatypes.S m + Datatypes.S m)%nat by lia.
    rewrite (q_pow_add t (Datatypes.S m) (Datatypes.S m)).
    rewrite <- (bk_q_pow_mul t t (Datatypes.S m)).
    ring.
Qed.

(* ============================================================ *)
(* §C 主件④⑤⑥：截断积分精确值 + 单调链（pm_ 面）+ 正性                   *)
(* ============================================================ *)

Fixpoint bv_zeros (L : nat) : list Q :=
  match L with
  | 0 => nil
  | Datatypes.S m => 0%Q :: bv_zeros m
  end.

Lemma bv_zeros_length : forall L : nat, length (bv_zeros L) = L.
Proof.
  induction L as [| l IH].
  - reflexivity.
  - cbn [bv_zeros length]. rewrite IH. reflexivity.
Qed.

Lemma bv_zeros_int : forall (L k : nat), pint_integral_from (bv_zeros L) k == 0%Q.
Proof.
  induction L as [| l IH]; intros k.
  - reflexivity.
  - cbn [bv_zeros pint_integral_from]. unfold pint_monomial_int.
    rewrite pint_zero_div, Qplus_0_l. apply IH.
Qed.

Theorem bv_zeros_int0 : forall L : nat, pint_integral (bv_zeros L) == 0%Q.
Proof. intro L. unfold pint_integral. apply bv_zeros_int. Qed.

Lemma bv_c_pos_le : forall n m : nat, QleT' 0 ((Z.of_nat (bkC (n + m) n) # 1)%Q).
Proof.
  intros n m. apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
  assert (Hb : 1 <= bkC (n + m) n) by (apply bkC_pos; lia).
  assert (Hz : (0 <= Z.of_nat (bkC (n + m) n))%Z) by apply Nat2Z.is_nonneg.
  lia.
Qed.

Lemma bv_pos_cint : forall n m : nat,
  QleT' 0 (pint_integral (pei_list (n + 2 * m) (2 * n + 1))).
Proof.
  intros n m. apply Qle_to_QleT'. apply Qlt_le_weak. apply pei_beta_pos.
Qed.

(* 主件④：截断积分 == 级数部分和（精确 QeqT） *)
Theorem bv_carrier_value : forall n M : nat,
  pint_integral (bv_carrier n M) == sum_upto (Datatypes.S M) (fun m : nat => bv_term n m).
Proof.
  intros n M. induction M as [| m IH].
  - change (bv_carrier n 0)
      with (pint_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                       (pei_list (n + 2 * 0) (2 * n + 1))).
    change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + 0) n) # 1)%Q)
                                   (pei_list (n + 2 * 0) (2 * n + 1)))).
    rewrite pei_beta_value. unfold bv_term.
    replace (n + 2 * 0)%nat with n%nat by lia.
    replace (3 * n + 2 * 0 + 2)%nat with (n + (2 * n + 1) + 1)%nat by lia.
    ring.
  - change (bv_carrier n (Datatypes.S m))
      with (pint_add (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                    (bv_pad (bv_carrier n m))).
    change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    assert (HL : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n m))).
    { rewrite pei_scale_length, pei_list_length, bv_pad_length, bv_carrier_length. lia. }
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HL)).
    rewrite bv_pad_int.
    rewrite (qeqT_imp_qeq _ _
              (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S m) n) # 1)%Q)
                                   (pei_list (n + 2 * Datatypes.S m) (2 * n + 1)))).
    rewrite pei_beta_value, IH. unfold bv_term.
    replace ((n + 2 * Datatypes.S m) + (2 * n + 1) + 1)%nat
      with (3 * n + 2 * Datatypes.S m + 2)%nat by lia.
    ring.
Qed.

(* 主件⑤：截断积分单调链（消费 PintMono：pm_scale_mono/pm_add_mono/
   pm_qle_wd_l/pm_qle_wd_r——线性/单调面承载） *)
Theorem bv_sum_mono : forall n M : nat,
  QleT' (pint_integral (bv_carrier n M))
        (pint_integral (bv_carrier n (Datatypes.S M))).
Proof.
  intros n M.
  change (pint_integral (bv_carrier n (Datatypes.S M)))
    with (pint_integral (pint_add
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)))).
  assert (Hlen : length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                    (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                 = length (bv_pad (bv_carrier n M))).
  { rewrite pei_scale_length, pei_list_length, bv_pad_length, bv_carrier_length. lia. }
  assert (HId1 : Id (length (bv_zeros (3 * n + 2 * M + 2 + 2)))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite bv_zeros_length, bv_pad_length, bv_carrier_length. reflexivity. }
  assert (HId2 : Id (length (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                    (length (bv_pad (bv_carrier n M)))).
  { rewrite <- Hlen. reflexivity. }
  (* 0 ≤ ∫X（pm_scale_mono + Beta 正 + 零表换形） *)
  assert (HleX : QleT' 0 (pint_integral
                    (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))).
  { apply (pm_qle_wd_r
             (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
               pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
             (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                        (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
             0%Q).
    - apply Qeq_sym. apply qeqT_imp_qeq.
      apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                 (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
    - apply (pm_qle_wd_l
               (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                          (bv_zeros (3 * n + 2 * M + 2 + 2))))
               0%Q
               (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                 pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)).
      + transitivity (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                       pint_integral (bv_zeros (3 * n + 2 * M + 2 + 2)))%Q).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (bv_zeros (3 * n + 2 * M + 2 + 2))).
        * rewrite bv_zeros_int0. apply Qmult_0_r.
      + apply (pm_qle_wd_r
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))))
                 (((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q *
                   pint_integral (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))%Q)
                 (pint_integral (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                            (bv_zeros (3 * n + 2 * M + 2 + 2))))).
        * apply qeqT_imp_qeq.
          apply (pint_integral_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                                     (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
        * apply (pm_scale_mono ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                   (bv_zeros (3 * n + 2 * M + 2 + 2))
                   (pei_list (n + 2 * Datatypes.S M) (2 * n + 1))).
          -- apply bv_c_pos_le.
          -- apply (pm_qle_wd_l 0%Q _ _).
             ++ apply Qeq_sym. apply bv_zeros_int0.
             ++ apply bv_pos_cint. }
  (* 载体 M 与 (零表 ⊕ 垫尾载体) 积分等形 *)
  assert (Hmove : pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                          (bv_pad (bv_carrier n M)))
                 == pint_integral (bv_carrier n M)).
  { assert (HLz : length (bv_zeros (3 * n + 2 * M + 2 + 2))
                  = length (bv_pad (bv_carrier n M)))
      by (rewrite bv_zeros_length, bv_pad_length, bv_carrier_length; reflexivity).
    rewrite (qeqT_imp_qeq _ _ (pint_integral_add _ _ HLz)).
    rewrite bv_zeros_int0, bv_pad_int. ring. }
  apply (pm_qle_wd_l
           (pint_integral (pint_add (bv_zeros (3 * n + 2 * M + 2 + 2))
                                    (bv_pad (bv_carrier n M))))
           (pint_integral (bv_carrier n M))
           (pint_integral (pint_add
                (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                            (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
                (bv_pad (bv_carrier n M))))).
  - exact Hmove.
  - apply (pm_add_mono (bv_zeros (3 * n + 2 * M + 2 + 2))
             (pint_scale ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1)%Q)
                         (pei_list (n + 2 * Datatypes.S M) (2 * n + 1)))
             (bv_pad (bv_carrier n M)) (bv_pad (bv_carrier n M))).
    + exact HId1.
    + exact HId2.
    + apply (pm_qle_wd_l 0%Q _ _).
      * apply Qeq_sym. apply bv_zeros_int0.
      * exact HleX.
    + apply qleT'_refl.
Qed.

(* 部分和严格正（Q 层归纳） *)
Lemma bv_sum_upto_pos : forall n M : nat,
  QltT 0 (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m)).
Proof.
  intros n. induction M as [| m IH].
  - change (sum_upto (Datatypes.S 0) (fun m0 : nat => bv_term n m0))
      with (0 + bv_term n 0)%Q.
    apply Qlt_to_QltT.
    apply (pei_qeq_lt (bv_term n 0) (0 + bv_term n 0)%Q 0%Q).
    + ring.
    + apply QltT_to_Qlt. apply bv_term_pos.
  - change (sum_upto (Datatypes.S (Datatypes.S m)) (fun m0 : nat => bv_term n m0))
      with (sum_upto (Datatypes.S m) (fun m0 : nat => bv_term n m0)
              + bv_term n (Datatypes.S m))%Q.
    apply Qlt_to_QltT. apply pei_lt_le_plus.
    + apply QltT_to_Qlt. exact IH.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply bv_term_pos.
Qed.

(* 主件⑥：截断积分严格正（I'_n ≥ 部分和 > 0 的 Q 层承载） *)
Theorem bv_sum_pos : forall n M : nat,
  QltT 0 (pint_integral (bv_carrier n M)).
Proof.
  intros n M. apply Qlt_to_QltT.
  apply (pei_qeq_lt (sum_upto (Datatypes.S M) (fun m : nat => bv_term n m))
                    (pint_integral (bv_carrier n M)) 0%Q).
  - apply Qeq_sym. apply bv_carrier_value.
  - apply QltT_to_Qlt. apply bv_sum_upto_pos.
Qed.

(* ============================================================ *)
(* §D 主件①：ln2 系数离散核（升幂 Delannoy == q̃_n）                      *)
(*   bv_D_asc n == Σ_{a≤n} C(n,a)²·2^a（bk_psd 镜像承载）；              *)
(*   手算链：[u^n](u−1)ⁿ(2−u)ⁿ = Σ_{a+b=n} C(n,a)C(n,b)2^{n−b}(−1)^{n+j} *)
(*   （j=n 时符号 (−1)^{2n−2a}=1）= Σ_a C(n,a)²2^a = D_n = q̃_n。         *)
(* ============================================================ *)

Definition bv_D_asc (n : nat) : nat :=
  bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n).

Theorem bv_delannoy_eq_qtilde : forall n : nat,
  QeqT ((Z.of_nat (bv_D_asc n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. apply qeq_imp_qeqT. unfold bv_D_asc.
  assert (H : bk_psd (fun k => bkC n (n - k) * bkC n (n - k)) (Datatypes.S n)
              = bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n)).
  { apply bk_psd_ext. intros k Hk.
    rewrite (bk_Qn_sym n k) by lia. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* ============================================================ *)
(* §E 主件⑦：分子闭式（Laurent 符号和）与定形锚组                          *)
(*   p_n = −Σ_{j≠n} c_j·(2^{j−n}−1)/(j−n)（手算 p: 0, 2, 9, 131/3）。     *)
(* ============================================================ *)

Fixpoint bv_negpow (k : nat) : Q :=
  match k with
  | 0 => 1%Q
  | Datatypes.S k' => (- bv_negpow k')%Q
  end.

(* 2 的带符号幂（Z 指数） *)
Definition bv_q2 (k : Z) : Q :=
  match Z.leb 0 k with
  | true => q_pow (2 # 1)%Q (Z.to_nat k)
  | false => 1%Q / q_pow (2 # 1)%Q (Z.to_nat (Z.opp k))
  end.

(* Laurent 系数 c_j = (−1)^{n+j}·Σ_{a≤j, a≤n, j−a≤n} C(n,a)C(n,j−a)2^{n−(j−a)} *)
Definition bv_c (n j : nat) : Q :=
  bv_negpow (n + j) *
  bk_psQ (fun a : nat =>
            if andb (Nat.leb a n) (Nat.leb (j - a) n)
            then ((Z.of_nat (bkC n a * bkC n (j - a)) # 1) *
                  q_pow (2 # 1)%Q (n - (j - a)))%Q
            else 0%Q)
         (Datatypes.S j) 1%Q.

(* 分子闭式 *)
Definition bv_p (n : nat) : Q :=
  (- bk_psQ (fun j : nat =>
               if Nat.eqb j n then 0%Q
               else (bv_c n j *
                     ((bv_q2 (Z.of_nat j - Z.of_nat n)%Z - 1%Q) /
                      ((Z.of_nat j - Z.of_nat n)%Z # 1))%Q))
            (Datatypes.S (2 * n)) 1%Q)%Q.

(* 真归一近似子 x_n := p_n/q̃_n（定形：无 2 幂） *)
Definition bv_x (n : nat) : Q := bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q.

(* 2 幂归一形 x''_n := p_n/(2^n·q̃_n)（死亡对照形） *)
Definition bv_x2pow (n : nat) : Q :=
  bv_p n / (q_pow (2 # 1)%Q n * (Z.of_nat (bk_Qn_qtilde n) # 1))%Q.

(* ---- 数值锚组（vm_compute 档）---- *)

Theorem bv_q1_anchor : QeqT ((Z.of_nat (bk_Qn_qtilde 1) # 1)%Q) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c11_anchor : QeqT (bv_c 1 1) (3 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c22_anchor : QeqT (bv_c 2 2) (13 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_c33_anchor : QeqT (bv_c 3 3) (63 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p0_anchor : QeqT (bv_p 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p1_anchor : QeqT (bv_p 1) (2 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p2_anchor : QeqT (bv_p 2) (9 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_p3_anchor : QeqT (bv_p 3) (131 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x0_anchor : QeqT (bv_x 0) 0%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x1_anchor : QeqT (bv_x 1) (2 # 3)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Theorem bv_x2_anchor : QeqT (bv_x 2) (9 # 13)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 跨变体核对：r_2 == 2^{3}·p_2（D016 r: 0, 8, 72） *)
Theorem bv_cross2_anchor : QeqT ((bv_p 2 * (Z.of_nat 8 # 1))%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 2 幂归一死亡分离见证：x''_1 = 1/3 < 2/3 = x_1（QltT Set 面） *)
Theorem bv_x2pow_sep1 : QltT (bv_x2pow 1) (bv_x 1).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 假设审计留痕：Print Assumptions（G4 复核位）                          *)
(* ============================================================ *)

Print Assumptions bv_delannoy_eq_qtilde.
Print Assumptions bv_term_pos.
Print Assumptions bv_carrier_eval.
Print Assumptions bv_carrier_value.
Print Assumptions bv_sum_mono.
Print Assumptions bv_sum_pos.
Print Assumptions bv_p3_anchor.
Print Assumptions bv_x2pow_sep1.
