(* ===================================================================== *)
(*  abl_z3_itg_carrier.v —— ζ(3) 三重积分族的迭代三次单积分承载机           *)
(* ===================================================================== *)
(*  使命：                                                            *)
(*    把 Beukers 1979 ζ(3) 三重积分被积族的 Taylor 截断（切片               *)
(*    abl_z2_truncfam 的 zb2_ps）落到三次单积分的载体上。段 = 有理系数      *)
(*    ×（x 多项式, y 多项式, z 多项式），段上先 z 后 y 后 x 施加三次        *)
(*    [0,1] 多项式定积分算子 pint_integral，证得：                         *)
(*      ① 段的三重积分值 = C(n+m,n)·B(n+m,n)³（B 由 t^a(1−t)^b 的系数表    *)
(*         积分闭式给出）——此即三次单积分施加，免任何交换积分次序引理；      *)
(*      ② 段列的逐点求值 = (x(1−x))ⁿ(y(1−y))ⁿ(z(1−z))ⁿ·zb2_ps n M (xyz)    *)
(*         （Taylor 截断被积式）；                                        *)
(*      ③ 段列积分和 = Σ_{m≤M} C(n+m,n)·B(n+m,n)³，且每项严格正。           *)
(*        聚合为单一系数表的整族积分面：因子表长度随段指标增长，逐项相加     *)
(*        将错位 Horner 位置，本件不含该聚合面（ζ(2) 面同款边界）。          *)
(*  依赖：                                                            *)
(*    Stdlib（QArith/ZArith/Arith/Lia）；缓存根 S01_BaseRing、             *)
(*    S02_CauchyComplete、S03_QExp、BeukersLists、PolyIntegral、           *)
(*    PadeErrorIntegral；池内切片件 abl_z2_truncfam（zb2_ps）与             *)
(*    abl_z2_itg_carrier（zb2_q_pow_mul）。零外部证书器、零实数层、         *)
(*    零经典逻辑。                                                        *)
(*  对标：                                                            *)
(*    Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.        *)
(*    London Math. Soc. 11 (1979) 中 ζ(3) 积分的迭代积分表示。              *)
(*  构造性：                                                          *)
(*    纯构造性、零假设声明、零承认词面；主语句面为 Qeq 等式与 Set 层        *)
(*    严格正见证 QltT；正性由二项系数非负、阶乘为正与 Beta 积分值的        *)
(*    正性闭式逐项复合。                                                  *)
(* ===================================================================== *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" abl_z3_itg_carrier.v（经温控包裹）。            *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_truncfam.
Require Import abl_z2_itg_carrier.

Open Scope Q_scope.
Open Scope list_scope.

(* ============================================================ *)
(* §0 基础小件：三变量幂的乘法分配                                      *)
(* ============================================================ *)

(* (xyz)^k = x^k·y^k·z^k（对 k 归纳，步档 ring 封闭） *)
Lemma zb3_qpow3 : forall (x y z : Q) (k : nat),
  q_pow (x * y * z) k == q_pow x k * q_pow y k * q_pow z k.
Proof.
  intros x y z k. induction k as [| k IH].
  - reflexivity.
  - rewrite (q_pow_succ (x * y * z) k), (q_pow_succ x k), (q_pow_succ y k),
      (q_pow_succ z k), IH. ring.
Qed.

(* ============================================================ *)
(* §1 承载定义（接口面，签名定死）                                      *)
(* ============================================================ *)

Definition zb3_seg : Set := (Q * (list Q * (list Q * list Q)))%type.

(* 第 m 段的规范载体：系数 C(n+m,n) 与因子表 t^{n+m}(1−t)^n 的三份拷贝 *)
Definition zb3_segof (n m : nat) : zb3_seg :=
  ((Z.of_nat (bkC (n + m) n) # 1)%Q,
   (pei_list (n + m) n,
    (pei_list (n + m) n, pei_list (n + m) n))).

(* 段列：头为 m = M，降序至 m = 0 *)
Fixpoint zb3_segl (n M : nat) : list zb3_seg :=
  match M with
  | O => ((Z.of_nat (bkC (n + 0) n) # 1,
           (pei_list (n + 0) n,
            (pei_list (n + 0) n, pei_list (n + 0) n))) :: nil)%list
  | Datatypes.S M' =>
      (Z.of_nat (bkC (n + Datatypes.S M') n) # 1,
       (pei_list (n + Datatypes.S M') n,
        (pei_list (n + Datatypes.S M') n,
         pei_list (n + Datatypes.S M') n))) :: zb3_segl n M'
  end.

(* 段的逐点求值：系数 × x 因子表 Horner 值 × y 因子表 Horner 值
   × z 因子表 Horner 值 *)
Definition zb3_beval (s : zb3_seg) (x y z : Q) : Q :=
  fst s * pint_eval (fst (snd s)) x
        * pint_eval (fst (snd (snd s))) y
        * pint_eval (snd (snd (snd s))) z.

(* 段列逐点求值（逐段相加） *)
Fixpoint zb3_beval_l (l : list zb3_seg) (x y z : Q) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb3_beval s x y z + zb3_beval_l l' x y z
  end.

(* z 积分算子：段 → 系数×（x 表, y 表）对 *)
Definition zb3_zint (s : zb3_seg) : (Q * (list Q * list Q))%type :=
  (fst s * pint_integral (snd (snd (snd s))),
   (fst (snd s), fst (snd (snd s)))).

(* y 积分算子：对 → x 多项式（系数 = 系数×z 积分值×y 积分值） *)
Definition zb3_yint (p : (Q * (list Q * list Q))) : list Q :=
  pint_scale (fst p * pint_integral (snd (snd p))) (fst (snd p)).

(* 段的迭代三重积分：对 x 多项式再施加一次积分算子 *)
Definition zb3_di (s : zb3_seg) : Q := pint_integral (zb3_yint (zb3_zint s)).

(* 段列积分和（逐段相加） *)
Fixpoint zb3_di_l (l : list zb3_seg) : Q :=
  match l with
  | nil => 0
  | s :: l' => zb3_di s + zb3_di_l l'
  end.

(* 第 m 项闭式：C(n+m,n)·B(n+m,n)³，B(a,n) = a!·n!/(a+n+1)! *)
Definition zb3_term (n m : nat) : Q :=
  (Z.of_nat (bkC (n + m) n) # 1)
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
    * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)).

(* 闭式项和：Σ_{m≤M} zb3_term n m *)
Fixpoint zb3_Isum (n M : nat) : Q :=
  match M with
  | O => zb3_term n 0
  | Datatypes.S M' => zb3_Isum n M' + zb3_term n (Datatypes.S M')
  end.

(* ============================================================ *)
(* §2 核心语句：段的三次单积分值、段列和、逐点面、正性                    *)
(* ============================================================ *)

(* 段的迭代三重积分闭式：先 z 后 y 后 x 三次单积分。
   z、y 积分给出系数 c·B·B，x 积分对缩放后的因子表再乘 B。 *)
Lemma zb3_di_seg_eq : forall n m, zb3_di (zb3_segof n m) == zb3_term n m.
Proof.
  intros n m. unfold zb3_di, zb3_yint, zb3_zint, zb3_segof, zb3_term.
  cbn [fst snd].
  assert (Hs := qeqT_imp_qeq _ _
             (pint_integral_scale
               (((Z.of_nat (bkC (n + m) n) # 1)
                 * pint_integral (pei_list (n + m) n))
                * pint_integral (pei_list (n + m) n))
               (pei_list (n + m) n))).
  rewrite Hs. rewrite (pei_beta_value (n + m) n). ring.
Qed.

(* 段列积分和 = 闭式项和（对 M 归纳） *)
Lemma zb3_di_l_segl : forall n M, zb3_di_l (zb3_segl n M) == zb3_Isum n M.
Proof.
  intros n M. induction M as [| M IH].
  - assert (H0 : zb3_segl n 0 = (zb3_segof n 0 :: nil)%list) by reflexivity.
    rewrite H0. cbn [zb3_di_l zb3_Isum].
    rewrite zb3_di_seg_eq. ring.
  - assert (HS : zb3_segl n (Datatypes.S M)
                 = (zb3_segof n (Datatypes.S M)) :: zb3_segl n M) by reflexivity.
    rewrite HS. cbn [zb3_di_l zb3_Isum].
    rewrite zb3_di_seg_eq. rewrite IH. ring.
Qed.

(* 逐点面：段列求值 = (x(1−x))ⁿ(y(1−y))ⁿ(z(1−z))ⁿ·zb2_ps n M (xyz)。
   段 m 贡献 C(n+m,n)·x^{n+m}(1−x)ⁿ·y^{n+m}(1−y)ⁿ·z^{n+m}(1−z)ⁿ，
   归入部分和末项。 *)
Lemma zb3_beval_segl : forall n M x y z,
  zb3_beval_l (zb3_segl n M) x y z
  == q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n
     * q_pow (z * (1 - z)) n * zb2_ps n M (x * y * z).
Proof.
  intros n M x y z. induction M as [| M IH].
  - assert (H0 : zb3_segl n 0 = (zb3_segof n 0 :: nil)%list) by reflexivity.
    rewrite H0. cbn [zb3_beval_l].
    unfold zb3_beval, zb3_segof. cbn [fst snd].
    rewrite (pei_beta_eval (n + 0) n x).
    rewrite (pei_beta_eval (n + 0) n y).
    rewrite (pei_beta_eval (n + 0) n z).
    rewrite !Nat.add_0_r. rewrite (bkC_diag n). cbn [Z.of_nat].
    rewrite zb2_ps_zero.
    rewrite <- (zb2_q_pow_mul x (1 - x) n).
    rewrite <- (zb2_q_pow_mul y (1 - y) n).
    rewrite <- (zb2_q_pow_mul z (1 - z) n).
    ring.
  - assert (HS : zb3_segl n (Datatypes.S M)
                 = (zb3_segof n (Datatypes.S M)) :: zb3_segl n M) by reflexivity.
    rewrite HS. cbn [zb3_beval_l].
    unfold zb3_beval, zb3_segof. cbn [fst snd].
    rewrite (pei_beta_eval (n + Datatypes.S M) n x).
    rewrite (pei_beta_eval (n + Datatypes.S M) n y).
    rewrite (pei_beta_eval (n + Datatypes.S M) n z).
    rewrite (q_pow_add x n (Datatypes.S M)).
    rewrite (q_pow_add y n (Datatypes.S M)).
    rewrite (q_pow_add z n (Datatypes.S M)).
    rewrite IH.
    rewrite zb2_ps_unfold.
    rewrite (zb3_qpow3 x y z (Datatypes.S M)).
    rewrite (zb2_q_pow_mul x (1 - x) n).
    rewrite (zb2_q_pow_mul y (1 - y) n).
    rewrite (zb2_q_pow_mul z (1 - z) n).
    ring.
Qed.

(* 第 m 项严格正：C(n+m,n) ≥ 1 与 Beta 值的分子阶乘、分母阶乘皆正 *)
Lemma zb3_term_pos : forall n m, QltT 0 (zb3_term n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold zb3_term.
  assert (Hc : Qlt 0 ((Z.of_nat (bkC (n + m) n) # 1))).
  { unfold Qlt. cbn [Qnum Qden Qmult Pos.mul].
    assert (Hb : (1 <= bkC (n + m) n)%nat) by (apply bkC_pos; lia).
    lia. }
  assert (Hbeta : Qlt 0 (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  { exact (pei_qeq_lt _ _ 0 (pei_beta_value (n + m) n) (pei_beta_pos (n + m) n)). }
  apply (Qmult_lt_0_compat
           ((Z.of_nat (bkC (n + m) n) # 1)
            * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))
            * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
           (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1))).
  - apply (Qmult_lt_0_compat
             ((Z.of_nat (bkC (n + m) n) # 1)
              * (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
             (q_fact (n + m) * q_fact n / q_fact (n + m + n + 1)))
    ; [ apply (Qmult_lt_0_compat _ _); assumption | exact Hbeta ].
  - exact Hbeta.
Qed.

(* 闭式项和严格正：首项严格正，逐项累加非负项保持严格正 *)
Lemma zb3_Isum_pos : forall n M, QltT 0 (zb3_Isum n M).
Proof.
  intros n M. induction M as [| M IH].
  - apply zb3_term_pos.
  - cbn [zb3_Isum]. apply Qlt_to_QltT.
    apply pei_lt_le_plus.
    + apply QltT_to_Qlt. exact IH.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply zb3_term_pos.
Qed.

(* ============================================================ *)
(* §3 数值锚（计算链判定件·辅助面豁免）                                  *)
(* ============================================================ *)

(* n = 1, m = 0：C(1,1)·B(1,1)³ = 1·(1/6)³ = 1/216 *)
Lemma zb3_term_1_0_anchor : zb3_term 1 0 == (1 # 216).
Proof. vm_compute. reflexivity. Qed.

(* n = 2, m = 1：C(3,2)·B(3,2)³ = 3·(1/60)³ = 1/72000 *)
Lemma zb3_term_2_1_anchor : zb3_term 2 1 == (1 # 72000).
Proof. vm_compute. reflexivity. Qed.

(* Isum 1 1 = 1/216 + 1/864 = 5/864（ζ(3) − 1 的截断首两项） *)
Lemma zb3_Isum_1_1_anchor : zb3_Isum 1 1 == (5 # 864).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §4 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions zb3_qpow3.
Print Assumptions zb3_di_seg_eq.
Print Assumptions zb3_di_l_segl.
Print Assumptions zb3_beval_segl.
Print Assumptions zb3_term_pos.
Print Assumptions zb3_Isum_pos.
Print Assumptions zb3_term_1_0_anchor.
Print Assumptions zb3_term_2_1_anchor.
Print Assumptions zb3_Isum_1_1_anchor.
