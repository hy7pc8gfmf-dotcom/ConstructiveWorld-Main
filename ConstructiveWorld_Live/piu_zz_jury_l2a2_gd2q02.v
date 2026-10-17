(*
  piu_zz_jury_l2a2_gd2q02.v — L2a continuation slice: ALT alternating toolkit,
  quadratic-instance bridge, and the UNFROZEN common-root bridge; slice
  on top of piu_zz_jury_l2a_gd2q01 (refit
  波新锚〔11 条 qeqT 化〕, read-only heritage).

  使命（Q01 冻结清单下切片·机械活）：
   (A) 二次实例桥（度 2 全桥）：f(X)=X^2+aX+b 与反演多项式 h(X)=X^2*f(r^2/X)
       =bX^2+a r^2 X+r^4 的 4x4 Sylvester 转置取向矩阵（sylv2T），核向量
       w=(z^3,z^2,z,1) 逐列读出 z*f, f, z*h, h 四条 eval 恒等式，
       combo（第 4 行替换保行列式）+ 零行湮灭 => 公共根 ⟹ 结式零，
       度 2 全称桥。
   (B) ALT-1..3 交替性工具包（6x6 泛型条目 specific-instance，cbn+ring）：
       ALT-1 相邻行（末两行）交换反号；ALT-2 两等行 ⟹ 零；
       ALT-3 行加他行倍数保行列式（首行向与装配所需末行向各一件）。
   (C) combo6（ALT-4 装配第一步，五次 ALT-3 合成为单一环恒等式：sylvT 第 6 行
       换成降幂权组合 (z^2 f, z f, f, z^2 h, z h, h)——六件 Q01 eval 恒等式
       即其语义凭证）+ M1z 零行湮灭（ALT-4 末步）=> 主桥
       piu_zz_l2a_common_root_resultant_zero 以 piu_zz_jury_l2a_gd2q01 原句形装成。
       证法：combo 为纯环恒等式（重复行行列式逐项相消），零湮灭经
       cbn 展开 + rewrite(Qeq setoid 穿透 unfold 后的显式多项式形) + ring。
   (D) 引擎实例闭合（r=25000）：主桥在 piu_zz_Ainf/Binf/Cinf/
       piu_zz_jury_engine_radius 直接实例化（零新增环成本），再以
       vm_compute+discriminate 纯计算收 no-common-root 闭包——与 Q01 已
       born 的 QneqT 非零判定面（Set 承载，遗产件在册）合流：
       L2a-alpha 引擎实例面双向闭合。

  构造性：全语句 Set 承载；计算收尾 vm_compute+ring；零 Axiom/Admitted。
  依赖：Stdlib QArith, Qring, Lia, List；池内件 piu_zz_poincare_engine、
  piu_zz_jury_cubic、piu_zz_jury_l2a_gd2q01（qdet/sylvT/rev_poly/resultant/
  六件 eval/QneqT 判定实例——全部只读引用）与 piu_zz_gauss_pair
  （qeqT/qeqT_intro——refit 波新增：4 条 qeval 恒等式 Set 皿载体）。
  域外注记（承 Q01，非债务）：「结式零 ⟹ 存在公共根」需代数闭包（FTA）；
  「圆 |z|=r 上无根」读法需复共轭；Q 世界诚实形=公共根形桥+QneqT 非零实例。
  编译配方：cpu_guard 包裹下 rocq c -native-compiler no -q -Q . "" 本件
  （依赖链 engine/jury_cubic/l2a_gd2q01 之 .vo 已在）。
*)

From Stdlib Require Import QArith Qring Lia List.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_jury_cubic.
Require Import piu_zz_jury_l2a_gd2q01.
Require Import piu_zz_gauss_pair.

(* ================================================================== *)
(* Part A. 二次实例桥（度 2 全桥）.                                      *)
(* ================================================================== *)

Definition piu_zz_l2a2_row4 (x1 x2 x3 x4 : Q) : list Q :=
  cons x1 (cons x2 (cons x3 (cons x4 nil))).

(* f(X) = X^2 + aX + b 和它的反演 h(X) = X^2 * f(r^2/X) = bX^2 + a r^2 X + r^4. *)
Definition piu_zz_l2a2_qpoly (a b z : Q) : Q := (z*z + a*z + b)%Q.
Definition piu_zz_l2a2_qrev (a b r z : Q) : Q :=
  (b*(z*z) + a*(r*r)*z + (r*r*r*r))%Q.

(* 4x4 Sylvester matrix of f and h, transposed orientation (rows = classical
   columns), same architecture as the 6x6 cubic sylvT of Q01. *)
Definition piu_zz_l2a2_sylv2T (a b r : Q) : list (list Q) :=
  cons (piu_zz_l2a2_row4 1 0 b 0)
    (cons (piu_zz_l2a2_row4 a 1 (a*(r*r)) b)
      (cons (piu_zz_l2a2_row4 b a (r*r*r*r) (a*(r*r)))
        (cons (piu_zz_l2a2_row4 0 b 0 (r*r*r*r)) nil))).

(* Kernel vector w = (z^3, z^2, z, 1): the four column sums read
   z*f, f, z*h, h — the degree-2 analogues of Q01's six born eval lemmas. *)

Lemma piu_zz_l2a2_qeval_f1 : forall (a b r z : Q),
  qeqT ((1*(z*z*z) + a*(z*z) + b*z + 0*1)%Q)
       ((z*(piu_zz_l2a2_qpoly a b z))%Q).
Proof. intros a b r z. apply qeqT_intro. unfold piu_zz_l2a2_qpoly. ring. Qed.

Lemma piu_zz_l2a2_qeval_f2 : forall (a b r z : Q),
  qeqT ((0*(z*z*z) + 1*(z*z) + a*z + b*1)%Q)
       ((piu_zz_l2a2_qpoly a b z)%Q).
Proof. intros a b r z. apply qeqT_intro. unfold piu_zz_l2a2_qpoly. ring. Qed.

Lemma piu_zz_l2a2_qeval_h1 : forall (a b r z : Q),
  qeqT ((b*(z*z*z) + a*(r*r)*(z*z) + (r*r*r*r)*z + 0*1)%Q)
       ((z*(piu_zz_l2a2_qrev a b r z))%Q).
Proof. intros a b r z. apply qeqT_intro. unfold piu_zz_l2a2_qrev. ring. Qed.

Lemma piu_zz_l2a2_qeval_h2 : forall (a b r z : Q),
  qeqT ((0*(z*z*z) + b*(z*z) + a*(r*r)*z + (r*r*r*r)*1)%Q)
       ((piu_zz_l2a2_qrev a b r z)%Q).
Proof. intros a b r z. apply qeqT_intro. unfold piu_zz_l2a2_qrev. ring. Qed.

(* M1q: rows 1-3 of sylv2T kept; row 4 := (z*f, f, z*h, h) — the weighted
   combination with coefficient-1 row as target.  M1q_z: the same matrix
   with the row-4 entries in the rewrite-product zero shape. *)
Definition piu_zz_l2a2_M1q (a b r z : Q) : list (list Q) :=
  cons (piu_zz_l2a2_row4 1 0 b 0)
    (cons (piu_zz_l2a2_row4 a 1 (a*(r*r)) b)
      (cons (piu_zz_l2a2_row4 b a (r*r*r*r) (a*(r*r)))
        (cons (piu_zz_l2a2_row4 (z*(z*z + a*z + b))%Q (z*z + a*z + b)%Q
                       (z*(b*(z*z) + a*(r*r)*z + (r*r*r*r)))%Q
                       (b*(z*z) + a*(r*r)*z + (r*r*r*r))%Q) nil))).

Definition piu_zz_l2a2_M1q_z (a b r z : Q) : list (list Q) :=
  cons (piu_zz_l2a2_row4 1 0 b 0)
    (cons (piu_zz_l2a2_row4 a 1 (a*(r*r)) b)
      (cons (piu_zz_l2a2_row4 b a (r*r*r*r) (a*(r*r)))
        (cons (piu_zz_l2a2_row4 (z*0)%Q 0%Q (z*0)%Q 0%Q) nil))).

(* combo at degree 2: replacing row 4 by the weighted combination preserves
   the determinant (fused ALT-3 instances; raw ring identity). *)
Time Lemma piu_zz_l2a2_quad_combo : forall (a b r z : Q),
  piu_zz_l2a_qdet 4 (piu_zz_l2a2_sylv2T a b r)
  == piu_zz_l2a_qdet 4 (piu_zz_l2a2_M1q a b r z).
Proof. intros a b r z. unfold piu_zz_l2a2_sylv2T, piu_zz_l2a2_M1q,
  piu_zz_l2a2_row4. cbn. ring. Qed.

(* zero-row cofactor vanishing at the M1q_z shape (cbn+ring, Q01 同技). *)
Time Lemma piu_zz_l2a2_quad_M1z_zero : forall (a b r z : Q),
  piu_zz_l2a_qdet 4 (piu_zz_l2a2_M1q_z a b r z) == 0%Q.
Proof. intros a b r z. unfold piu_zz_l2a2_M1q_z, piu_zz_l2a2_row4. cbn. ring. Qed.

(* 度 2 全桥：公共根 ⟹ 结式零（Q01 冻结清单「二次实例桥」解冻 born）. *)
Time Theorem piu_zz_l2a2_quad_common_root_resultant_zero :
  forall (a b r z : Q),
    (piu_zz_l2a2_qpoly a b z == 0)%Q ->
    (piu_zz_l2a2_qrev a b r z == 0)%Q ->
    (piu_zz_l2a_qdet 4 (piu_zz_l2a2_sylv2T a b r) == 0)%Q.
Proof.
  intros a b r z Hf Hh. eapply Qeq_trans.
  - apply piu_zz_l2a2_quad_combo.
  - unfold piu_zz_l2a2_M1q. cbn.
    unfold piu_zz_l2a2_qpoly in Hf. unfold piu_zz_l2a2_qrev in Hh.
    rewrite Hf, Hh. ring.
Qed.

(* ================================================================== *)
(* Part B. ALT-1..3 alternating toolkit, generic-entry 6x6 instances.   *)
(* (specific-instance cbn+ring route certified by Q01; each closes in    *)
(* milliseconds — the entries are left fully generic so the toolkit is   *)
(* reusable beyond the sylvT instance).                                  *)
(* ================================================================== *)

Definition piu_zz_l2a2_r6 (x1 x2 x3 x4 x5 x6 : Q) : list Q :=
  cons x1 (cons x2 (cons x3 (cons x4 (cons x5 (cons x6 nil))))).

(* ALT-1: swapping the adjacent (last two) rows flips the determinant sign. *)
Time Lemma piu_zz_l2a_alt1_swap_adjacent56 :
  forall (a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
          c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
          e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6 : Q),
  piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 a1 a2 a3 a4 a5 a6)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 e1 e2 e3 e4 e5 e6)
              (cons (piu_zz_l2a2_r6 f1 f2 f3 f4 f5 f6) nil))))))
  == (-1)%Q * piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 a1 a2 a3 a4 a5 a6)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 f1 f2 f3 f4 f5 f6)
              (cons (piu_zz_l2a2_r6 e1 e2 e3 e4 e5 e6) nil)))))).
Proof.
  intros a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
         c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
         e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6.
  unfold piu_zz_l2a2_r6. cbn. ring.
Qed.

(* ALT-2: two equal rows force the determinant to vanish. *)
Time Lemma piu_zz_l2a_alt2_equal_rows56_zero :
  forall (a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
          c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
          u1 u2 u3 u4 u5 u6 : Q),
  piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 a1 a2 a3 a4 a5 a6)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 u1 u2 u3 u4 u5 u6)
              (cons (piu_zz_l2a2_r6 u1 u2 u3 u4 u5 u6) nil))))))
  == 0%Q.
Proof.
  intros a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
         c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
         u1 u2 u3 u4 u5 u6.
  unfold piu_zz_l2a2_r6. cbn. ring.
Qed.

(* ALT-3: adding a multiple of another row to a row preserves the
   determinant.  Two orientations, both needed bookkeeping-wise:
   (a) target row 1 (the frozen-checklist wording), (b) target row 6
   (the coefficient-1 row the assembly actually uses). *)
Time Lemma piu_zz_l2a_alt3_add_mult_row1 :
  forall (a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
          c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
          e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6 t : Q),
  piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 a1 a2 a3 a4 a5 a6)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 e1 e2 e3 e4 e5 e6)
              (cons (piu_zz_l2a2_r6 f1 f2 f3 f4 f5 f6) nil))))))
  == piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 (a1 + t*b1)%Q (a2 + t*b2)%Q (a3 + t*b3)%Q
                          (a4 + t*b4)%Q (a5 + t*b5)%Q (a6 + t*b6)%Q)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 e1 e2 e3 e4 e5 e6)
              (cons (piu_zz_l2a2_r6 f1 f2 f3 f4 f5 f6) nil)))))).
Proof.
  intros a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
         c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
         e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6 t.
  unfold piu_zz_l2a2_r6. cbn. ring.
Qed.

Time Lemma piu_zz_l2a_alt3_add_mult_row56 :
  forall (a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
          c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
          e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6 t : Q),
  piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 a1 a2 a3 a4 a5 a6)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 e1 e2 e3 e4 e5 e6)
              (cons (piu_zz_l2a2_r6 f1 f2 f3 f4 f5 f6) nil))))))
  == piu_zz_l2a_qdet 6
    (cons (piu_zz_l2a2_r6 a1 a2 a3 a4 a5 a6)
      (cons (piu_zz_l2a2_r6 b1 b2 b3 b4 b5 b6)
        (cons (piu_zz_l2a2_r6 c1 c2 c3 c4 c5 c6)
          (cons (piu_zz_l2a2_r6 d1 d2 d3 d4 d5 d6)
            (cons (piu_zz_l2a2_r6 e1 e2 e3 e4 e5 e6)
              (cons (piu_zz_l2a2_r6 (f1 + t*e1)%Q (f2 + t*e2)%Q
                            (f3 + t*e3)%Q (f4 + t*e4)%Q
                            (f5 + t*e5)%Q (f6 + t*e6)%Q) nil)))))).
Proof.
  intros a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
         c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6
         e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6 t.
  unfold piu_zz_l2a2_r6. cbn. ring.
Qed.

(* ================================================================== *)
(* Part C. combo6 + zero kill + THE UNFROZEN MAIN BRIDGE.               *)
(*                                                                      *)
(* M1_6 = sylvT with row 6 := (z^2 f, z f, f, z^2 h, z h, h) written in  *)
(* the explicit expanded z-polynomial forms (so that the hypotheses,     *)
(* after unfold, rewrite onto them verbatim).  The combo identity        *)
(* det(sylvT) == det(M1_6) is a raw ring identity: expanding by          *)
(* multilinearity in row 6, every extra term is a repeated-row           *)
(* determinant, which vanishes term-by-term (ALT-2 content).  The six    *)
(* born eval lemmas of Q01 are the semantic certificate that the new     *)
(* row 6 is exactly the kernel-vector column-sum vector (z^2 f, ...).    *)
(*                                                                      *)
(* Note (mechanics): rewrite with Qeq hypotheses cannot cross an opaque  *)
(* qdet application (no Proper instance registered for qdet), so the     *)
(* zero-kill first exposes the raw arithmetic by cbn and then rewrites;  *)
(* ring then annihilates the zero-coefficient monomials.  Both steps     *)
(* probe-verified in the probe domain before the first main shot.        *)
(* ================================================================== *)

Definition piu_zz_l2a2_M1_6 (a b c r z : Q) : list (list Q) :=
  cons (piu_zz_l2a_row6 1 0 0 c 0 0)
    (cons (piu_zz_l2a_row6 a 1 0 (b * (r * r)) c 0)
      (cons (piu_zz_l2a_row6 b a 1 (a * (r * r * r * r)) (b * (r * r)) c)
        (cons (piu_zz_l2a_row6 c b a (r * r * r * r * r * r)
                 (a * (r * r * r * r)) (b * (r * r)))
          (cons (piu_zz_l2a_row6 0 c b 0 (r * r * r * r * r * r)
                   (a * (r * r * r * r)))
            (cons (piu_zz_l2a_row6
                    ((z*z)*(z*z*z + a*(z*z) + b*z + c))%Q
                    (z*(z*z*z + a*(z*z) + b*z + c))%Q
                    (z*z*z + a*(z*z) + b*z + c)%Q
                    ((z*z)*(c*(z*z*z) + b*(r*r)*(z*z)
                             + a*(r*r*r*r)*z + r*r*r*r*r*r))%Q
                    (z*(c*(z*z*z) + b*(r*r)*(z*z)
                         + a*(r*r*r*r)*z + r*r*r*r*r*r))%Q
                    (c*(z*z*z) + b*(r*r)*(z*z)
                     + a*(r*r*r*r)*z + r*r*r*r*r*r)%Q) nil))))).

Definition piu_zz_l2a2_M1z_6 (a b c r z : Q) : list (list Q) :=
  cons (piu_zz_l2a_row6 1 0 0 c 0 0)
    (cons (piu_zz_l2a_row6 a 1 0 (b * (r * r)) c 0)
      (cons (piu_zz_l2a_row6 b a 1 (a * (r * r * r * r)) (b * (r * r)) c)
        (cons (piu_zz_l2a_row6 c b a (r * r * r * r * r * r)
                 (a * (r * r * r * r)) (b * (r * r)))
          (cons (piu_zz_l2a_row6 0 c b 0 (r * r * r * r * r * r)
                   (a * (r * r * r * r)))
            (cons (piu_zz_l2a_row6 ((z*z)*0)%Q (z*0)%Q 0%Q
                                   ((z*z)*0)%Q (z*0)%Q 0%Q) nil))))).

(* ALT-4 step 1 (combo): five fused ALT-3 applications. *)
Time Lemma piu_zz_l2a2_combo6 : forall (a b c r z : Q),
  piu_zz_l2a_qdet 6 (piu_zz_l2a_sylvT a b c r)
  == piu_zz_l2a_qdet 6 (piu_zz_l2a2_M1_6 a b c r z).
Proof.
  intros a b c r z.
  unfold piu_zz_l2a_sylvT, piu_zz_l2a2_M1_6, piu_zz_l2a_row6. cbn. ring.
Qed.

(* ALT-4 step 2: the zero-row cofactor vanishing at the M1z shape. *)
Time Lemma piu_zz_l2a2_M1z_zero6 : forall (a b c r z : Q),
  piu_zz_l2a_qdet 6 (piu_zz_l2a2_M1z_6 a b c r z) == 0%Q.
Proof. intros a b c r z. unfold piu_zz_l2a2_M1z_6, piu_zz_l2a_row6. cbn. ring. Qed.

(* THE MAIN BRIDGE, unfrozen at Q01's exact frozen statement shape. *)
Time Theorem piu_zz_l2a_common_root_resultant_zero :
  forall (a b c r z : Q),
    (piu_zz_jury_poly a b c z == 0)%Q ->
    (piu_zz_l2a_rev_poly a b c r z == 0)%Q ->
    (piu_zz_l2a_resultant a b c r == 0)%Q.
Proof.
  intros a b c r z Hf Hh. unfold piu_zz_l2a_resultant. eapply Qeq_trans.
  - apply piu_zz_l2a2_combo6.
  - unfold piu_zz_l2a2_M1_6. cbn.
    unfold piu_zz_jury_poly in Hf. unfold piu_zz_l2a_rev_poly in Hh.
    rewrite Hf, Hh. ring.
Qed.

(* ================================================================== *)
(* Part D. Engine instance closure at r = 25000.                        *)
(* (The generic bridge instantiates at the engine coefficients with zero *)
(* extra ring cost; the no-common-root closure is then pure computation  *)
(* and merges with Q01's born QneqT nonvanishing face.)                  *)
(* ================================================================== *)

Time Theorem piu_zz_l2a2_engine_common_root_resultant_zero :
  forall z : Q,
    (piu_zz_jury_poly piu_zz_Ainf piu_zz_Binf piu_zz_Cinf z == 0)%Q ->
    (piu_zz_l2a_rev_poly piu_zz_Ainf piu_zz_Binf piu_zz_Cinf
       piu_zz_jury_engine_radius z == 0)%Q ->
    (piu_zz_l2a_resultant_engine_value == 0)%Q.
Proof.
  intros z Hf Hh. unfold piu_zz_l2a_resultant_engine_value.
  apply (piu_zz_l2a_common_root_resultant_zero
           piu_zz_Ainf piu_zz_Binf piu_zz_Cinf
           piu_zz_jury_engine_radius z).
  exact Hf. exact Hh.
Qed.

(* Closure: the engine polynomial pair has NO common root — the bridge
   direction (this slice) plus the computed nonvanishing (Q01's QneqT
   face) meet; the last step is vm_compute + discriminate, no assumption. *)
Time Theorem piu_zz_l2a2_engine_no_common_root :
  forall z : Q,
    (piu_zz_jury_poly piu_zz_Ainf piu_zz_Binf piu_zz_Cinf z == 0)%Q ->
    (piu_zz_l2a_rev_poly piu_zz_Ainf piu_zz_Binf piu_zz_Cinf
       piu_zz_jury_engine_radius z == 0)%Q -> False.
Proof.
  intros z Hf Hh.
  assert (Hr : (piu_zz_l2a_resultant_engine_value == 0)%Q).
  { exact (piu_zz_l2a2_engine_common_root_resultant_zero z Hf Hh). }
  vm_compute in Hr. discriminate Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* Audit: assumption accounting and data-level extraction probe.        *)
(* ------------------------------------------------------------------ *)

Print Assumptions piu_zz_l2a2_qeval_f1.
Print Assumptions piu_zz_l2a2_qeval_f2.
Print Assumptions piu_zz_l2a2_qeval_h1.
Print Assumptions piu_zz_l2a2_qeval_h2.
Print Assumptions piu_zz_l2a2_quad_combo.
Print Assumptions piu_zz_l2a2_quad_M1z_zero.
Print Assumptions piu_zz_l2a2_quad_common_root_resultant_zero.
Print Assumptions piu_zz_l2a_alt1_swap_adjacent56.
Print Assumptions piu_zz_l2a_alt2_equal_rows56_zero.
Print Assumptions piu_zz_l2a_alt3_add_mult_row1.
Print Assumptions piu_zz_l2a_alt3_add_mult_row56.
Print Assumptions piu_zz_l2a2_combo6.
Print Assumptions piu_zz_l2a2_M1z_zero6.
Print Assumptions piu_zz_l2a_common_root_resultant_zero.
Print Assumptions piu_zz_l2a2_engine_common_root_resultant_zero.
Print Assumptions piu_zz_l2a2_engine_no_common_root.

Extraction "piu_zz_l2a2_gd2q02_data.ml" piu_zz_l2a2_sylv2T piu_zz_l2a2_qpoly
  piu_zz_l2a2_qrev piu_zz_l2a2_M1q piu_zz_l2a2_M1_6 piu_zz_l2a2_M1z_6.
