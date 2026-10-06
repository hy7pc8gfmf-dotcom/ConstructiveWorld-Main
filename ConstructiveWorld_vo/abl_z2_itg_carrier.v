(* ===================================================================== *)
(*  abl_z2_itg_carrier.v —— ζ(2) 有理性二重积分族的迭代积分承载机            *)
(*  模块名：abl_z2_itg_carrier。                                          *)
(*  使命：把二重积分被积族的 Taylor 截断（切片 abl_z2_truncfam 的 zb2_ps）   *)
(*        落到两次单积分的表示上。段 = 有理系数 ×（x 多项式, y 多项式），     *)
(*        段上先 y 后 x 施加两次 [0,1] 多项式定积分算子 pint_integral，      *)
(*        证得：① 段的二重积分值 = C(n+m,n)·B(n+m,n)²（B = Beta 积分值，    *)
(*        由 t^a(1−t)^b 的系数表积分闭式给出）——此即先 y 后 x 的两次单       *)
(*        积分施加，免任何交换积分次序引理；② 段列的逐点求值 =             *)
(*        (x(1−x))ⁿ(y(1−y))ⁿ·zb2_ps n M (xy)（Taylor 截断被积式）；          *)
(*        ③ 段列积分和 = Σ_{m≤M} C(n+m,n)·B(n+m,n)²，且每项严格正。         *)
(*        聚合为单一系数表的整族积分面：因子表长度随段指标增长，逐项相加      *)
(*        将错位 Horner 位置，本件不含该聚合面。                           *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia）；缓存根 S01_BaseRing、          *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists、PolyIntegral、        *)
(*        PadeErrorIntegral；池内切片件 abl_z2_truncfam（zb2_ps）。         *)
(*        零外部证书器、零实数层、零经典逻辑。                              *)
(*  构造性：纯构造性、零假设声明、零承认式语句、零悬置假设；主语句面为        *)
(*        Qeq 等式与 Set 层严格正见证 QltT；正性由二项系数非负、阶乘为正      *)
(*        与 Beta 积分值的正性闭式逐项复合，未引入有序域决策程序。           *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no           *)
(*        -Q vo_local_world_unified_0930 "" -Q . "" abl_z2_itg_carrier.v。 *)
(*  对标：Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.    *)
(*        London Math. Soc. 11 (1979) 中 I_n 的迭代积分表示与其多项式核。    *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_truncfam.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* §0 基础小件：幂的乘法分配与零档部分和                                *)
(* ============================================================ *)

(* 幂对乘法基的分配：(xy)^k = x^k·y^k *)
Lemma zb2_q_pow_mul : forall (x y : Q) (k : nat),
  q_pow (x * y) k == (q_pow x k * q_pow y k)%Q.
Proof.
  intros x y k. induction k as [| k IH].
  - reflexivity.
  - rewrite (q_pow_succ (x * y) k). rewrite (q_pow_succ x k).
    rewrite (q_pow_succ y k). rewrite IH. ring.
Qed.

(* 零档部分和恒为 1：Σ_{m≤0} C(n+m,n)t^m = C(n,n) = 1 *)
Lemma zb2_ps_zero : forall n t, zb2_ps n 0 t == 1.
Proof.
  intros n t. unfold zb2_ps. cbn [bk_psQ q_pow].
  rewrite Nat.add_0_r. rewrite (bkC_diag n). cbn [Z.of_nat]. ring.
Qed.

(* ============================================================ *)
(* §1 承载定义（接口面，签名定死）                                      *)
(* ============================================================ *)

Definition zb2_seg : Set := (Q * (list Q * list Q))%type.

(* 第 m 段的规范表示：系数 C(n+m,n) 与因子表 t^{n+m}(1−t)^n 的双份拷贝 *)
Definition zb2_segof (n m : nat) : zb2_seg :=
  ((Z.of_nat (bkC (n + m) n) # 1)%Q,
   (pei_list (n + m) n, pei_list (n + m) n)).

(* 段列：头为 m = M，降序至 m = 0 *)
Fixpoint zb2_segl (n M : nat) : list zb2_seg :=
  match M with
  | O => ((Z.of_nat (bkC (n + 0) n) # 1,
           (pei_list (n + 0) n, pei_list (n + 0) n)) :: nil)%list
  | Datatypes.S M' => (Z.of_nat (bkC (n + Datatypes.S M') n) # 1,
                       (pei_list (n + Datatypes.S M') n,
                        pei_list (n + Datatypes.S M') n)) :: zb2_segl n M'
  end.

(* 段的逐点求值：系数 × x 因子表 Horner 值 × y 因子表 Horner 值 *)
Definition zb2_beval (s : zb2_seg) (x y : Q) : Q :=
  fst s * pint_eval (fst (snd s)) x * pint_eval (snd (snd s)) y.

(* 段列逐点求值（逐段相加） *)
Fixpoint zb2_beval_l (l : list zb2_seg) (x y : Q) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb2_beval s x y + zb2_beval_l l' x y
  end.

(* y 积分算子：段 → x 多项式（系数 = 段系数 × y 因子表积分值） *)
Definition zb2_yint (s : zb2_seg) : list Q :=
  pint_scale (fst s * pint_integral (snd (snd s))) (fst (snd s)).

(* 段的迭代二重积分：对 x 多项式再施加一次积分算子 *)
Definition zb2_di (s : zb2_seg) : Q := pint_integral (zb2_yint s).

(* 段列积分和（逐段相加） *)
Fixpoint zb2_di_l (l : list zb2_seg) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb2_di s + zb2_di_l l'
  end.

(* 第 m 项闭式：C(n+m,n)·B(n+m,n)²，B(a,n) = a!·n!/(a+n+1)! *)
Definition zb2_term (n m : nat) : Q :=
  (Z.of_nat (bkC (n + m) n) # 1)
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)).

(* 闭式项和：Σ_{m≤M} zb2_term n m *)
Fixpoint zb2_Isum (n M : nat) : Q :=
  match M with
  | O => zb2_term n 0
  | Datatypes.S M' => zb2_Isum n M' + zb2_term n (Datatypes.S M')
  end.

(* ============================================================ *)
(* §2 核心语句：段的两次单积分值、段列和、逐点面、正性                    *)
(* ============================================================ *)

(* 段的迭代二重积分闭式：先 y 后 x 两次单积分。
   y 积分给出系数 c·B，x 积分对缩放后的因子表再乘 B，与两项闭式相符。 *)
Lemma zb2_di_seg_eq : forall n m, zb2_di (zb2_segof n m) == zb2_term n m.
Proof.
  intros n m. unfold zb2_di, zb2_yint, zb2_segof, zb2_term.
  cbn [fst snd].
  assert (Hs := qeqT_imp_qeq _ _
             (pint_integral_scale
               ((Z.of_nat (bkC (n + m) n) # 1)
                * pint_integral (pei_list (n + m) n))
               (pei_list (n + m) n))).
  rewrite Hs. rewrite (pei_beta_value (n + m) n). ring.
Qed.

(* 段列积分和 = 闭式项和（对 M 归纳） *)
Lemma zb2_di_l_segl : forall n M, zb2_di_l (zb2_segl n M) == zb2_Isum n M.
Proof.
  intros n M. induction M as [| M IH].
  - assert (H0 : zb2_segl n 0 = (zb2_segof n 0 :: nil)%list) by reflexivity.
    rewrite H0. cbn [zb2_di_l zb2_Isum].
    rewrite zb2_di_seg_eq. ring.
  - assert (HS : zb2_segl n (Datatypes.S M)
                 = (zb2_segof n (Datatypes.S M)) :: zb2_segl n M) by reflexivity.
    rewrite HS. cbn [zb2_di_l zb2_Isum].
    rewrite zb2_di_seg_eq. rewrite IH. ring.
Qed.

(* 逐点面：段列求值 = (x(1−x))ⁿ(y(1−y))ⁿ·zb2_ps n M (xy)。
   段 m 贡献 C(n+m,n)·x^{n+m}(1−x)ⁿ·y^{n+m}(1−y)ⁿ，归入部分和末项。 *)
Lemma zb2_beval_segl : forall n M x y,
  zb2_beval_l (zb2_segl n M) x y
  == q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n * zb2_ps n M (x * y).
Proof.
  intros n M x y. induction M as [| M IH].
  - assert (H0 : zb2_segl n 0 = (zb2_segof n 0 :: nil)%list) by reflexivity.
    rewrite H0. cbn [zb2_beval_l].
    unfold zb2_beval, zb2_segof. cbn [fst snd].
    rewrite (pei_beta_eval (n + 0) n x).
    rewrite (pei_beta_eval (n + 0) n y).
    rewrite !Nat.add_0_r. rewrite (bkC_diag n). cbn [Z.of_nat].
    rewrite zb2_ps_zero.
    rewrite (zb2_q_pow_mul x (1 - x) n).
    rewrite (zb2_q_pow_mul y (1 - y) n).
    ring.
  - assert (HS : zb2_segl n (Datatypes.S M)
                 = (zb2_segof n (Datatypes.S M)) :: zb2_segl n M) by reflexivity.
    rewrite HS. cbn [zb2_beval_l].
    unfold zb2_beval, zb2_segof. cbn [fst snd].
    rewrite (pei_beta_eval (n + Datatypes.S M) n x).
    rewrite (pei_beta_eval (n + Datatypes.S M) n y).
    rewrite (q_pow_add x n (Datatypes.S M)).
    rewrite (q_pow_add y n (Datatypes.S M)).
    rewrite IH.
    rewrite zb2_ps_unfold.
    rewrite (zb2_q_pow_mul x (1 - x) n).
    rewrite (zb2_q_pow_mul y (1 - y) n).
    rewrite (zb2_q_pow_mul x y (Datatypes.S M)).
    ring.
Qed.

(* 第 m 项严格正：C(n+m,n) ≥ 1 与 Beta 值的分子阶乘、分母阶乘皆正 *)
Lemma zb2_term_pos : forall n m, QltT 0 (zb2_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold zb2_term.
  assert (Hc : Qlt 0 ((Z.of_nat (bkC (n + m) n) # 1))).
  { unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    assert (Hb : (1 <= bkC (n + m) n)%nat) by (apply bkC_pos; lia).
    lia. }
  assert (Hbeta : Qlt 0 (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  { exact (pei_qeq_lt _ _ 0 (pei_beta_value (n + m) n) (pei_beta_pos (n + m) n)). }
  apply (Qmult_lt_0_compat
           ((Z.of_nat (bkC (n + m) n) # 1)
            * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
           (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  - apply Qmult_lt_0_compat; assumption.
  - exact Hbeta.
Qed.

(* 闭式项和严格正：首项严格正，逐项累加非负项保持严格正 *)
Lemma zb2_Isum_pos : forall n M, QltT 0 (zb2_Isum n M).
Proof.
  intros n M. induction M as [| M IH].
  - apply zb2_term_pos.
  - cbn [zb2_Isum]. apply Qlt_to_QltT.
    apply pei_lt_le_plus.
    + apply QltT_to_Qlt. exact IH.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply zb2_term_pos.
Qed.

(* ============================================================ *)
(* §3 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions zb2_di_seg_eq.
Print Assumptions zb2_di_l_segl.
Print Assumptions zb2_beval_segl.
Print Assumptions zb2_term_pos.
Print Assumptions zb2_Isum_pos.
