(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   real_cauchy_schwarz（原 L285，2 句强证）	*)
(* ============================================================ *)

(* ============================================================ *)
(* UpCS.v *)
(* *)
(* 目的： 有限和 Cauchy–Schwarz 不等式（Real 层，eps 版）。 *)
(* 主件： real_cauchy_schwarz_lt：(AB)^2 < AA·BB + eps 严格形；real_cauchy_schwarz 为其 le 收敛形。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： Q 层核经逐项配方（Lagrange 形）构造，零除法零判别式；零公理面、全 Qed、可提取。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpCS.v —— 有限和 Cauchy–Schwarz 不等式（Real 层，eps 版）      *)
(*                                                              *)
(* 数学目标（eps 版有限和 C-S）：                                 *)
(*   对 a b : list Real，记                                      *)
(*     AB := dotp a b = Σ a_i·b_i（内积）                        *)
(*     AA := sql a   = Σ a_i²,  BB := sql b = Σ b_i²（平方和）   *)
(*   则对任意严格正 eps：                                        *)
(*     (AB)² ≤ AA·BB + eps        （real_le，Or 编码）           *)
(* 更强：real_lt (AB)² (AA·BB + eps)（逐项 gap ≥ 0 + eps 下界      *)
(*   直接给出一致分离，无需分支）。                               *)
(*                                                              *)
(* 路线（Lagrange/逐项配方，构造性，零除法零判别式）：             *)
(*   Q 层核：  (dotpQ a b)² ≤ (sqlQ a)·(sqlQ b)  （归纳 + 配方）   *)
(*   逐点化：  real_plus/real_mult Defined 透明 → projT1 逐点      *)
(*   Real 层：real_lt 见证 = (eps 见证, N1, 逐点 QltT)；           *)
(*   关键观察：AA·BB − AB² 逐点 ≥ 0 对**每个**指标成立（纯 Q 计    *)
(*   算），故 gap_n + eps_n > e1 一致成立——real_lt 一步构造。      *)
(*                                                              *)
(*     real_le (AA·BB) (AB² + eps)（对任意 eps > 0）              *)
(*   是**假命题**（反例 a=[1,0], b=[0,1]：AA·BB = 1 > eps 可取    *)
(*   1/2，则 1 ≤ 0 + 1/2 不成立）；且与原稿自己的证明路线结论      *)
(*   "即 (AB)² ≤ AA·BB" 相矛盾。本文件按 C-S 的真实方向结果        *)
(*   real_le (AB²) (AA·BB + eps)，并在文末给出原方向的形式化反驳    *)
(*   （Not (...)，非平凡反例构造）。                              *)
(*                                                              *)
(* 红线：纯构造性；Set 层语句（real_lt/real_le Or 编码/real_eq）；  *)
(*   零公理、零搁置证明、零中止、零经典逻辑；全部 Qed 闭合；可提取。 *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring QArith.Qabs.
Require Import CW_ConstructiveWorld_219.

Open Scope Q_scope.

(* ========== CS1：内积（逐项相乘有限和） ====================== *)
Fixpoint dotp (a b : list Real) : Real :=
  match a, b with
  | x :: xs, y :: ys => real_plus (real_mult x y) (dotp xs ys)
  | _, _ => real_zero
  end.

(* ========== CS2：平方和 ====================================== *)
Fixpoint sql (a : list Real) : Real :=
  match a with
  | nil => real_zero
  | x :: rest => real_plus (real_mult x x) (sql rest)
  end.

(* ========== Q 层副本（逐点求值目标） ========================= *)
Fixpoint sqlQ (u : list Q) : Q :=
  match u with
  | nil => 0
  | x :: rest => x * x + sqlQ rest
  end.

Fixpoint dotpQ (u v : list Q) : Q :=
  match u, v with
  | x :: xs, y :: ys => x * y + dotpQ xs ys
  | _, _ => 0
  end.

(* ========== Q 层基本不等式（构造性，零经典公理） ============= *)

(* 平方非负：三分支 Qcompare（可判定序，构造性合法） *)
Lemma Qle_0_sq : forall x : Q, Qle 0 (x * x).
Proof.
  intro x.
  destruct (Qcompare 0 x) as [ | | ] eqn:Ec.
  - (* Eq：0 == x *)
    assert (Hx0 : 0 == x) by exact (proj2 (Qeq_alt 0 x) Ec).
    apply qeq_le. rewrite <- Hx0. ring.
  - (* Lt：0 < x，0·x ≤ x·x（乘右保序） *)
    assert (H0x : 0 <= x).
    { apply Qlt_le_weak. exact (proj2 (Qlt_alt 0 x) Ec). }
    apply (Qle_trans _ (0 * x)).
    + apply qeq_le. ring.
    + apply (Qmult_le_compat_r 0 x x); assumption.
  - (* Gt：x < 0，0 ≤ −x，且 (−x)·(−x) == x·x *)
    assert (Hlt : Qlt x 0).
    { apply (proj2 (Qlt_alt x 0)).
      rewrite <- Qcompare_antisym. rewrite Ec. reflexivity. }
    assert (Hneg : 0 <= - x).
    { exact (Qopp_le_compat x 0 (Qlt_le_weak x 0 Hlt)). }
    apply (Qle_trans _ ((- x) * (- x))).
    + apply (Qle_trans _ (0 * (- x))).
      * apply qeq_le. ring.
      * apply (Qmult_le_compat_r 0 (- x) (- x)); assumption.
    + apply qeq_le. ring.
Qed.

(* 平方和非负 *)
Lemma Qle_0_sqlQ : forall u : list Q, Qle 0 (sqlQ u).
Proof.
  induction u as [| x xs IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (0 + sqlQ xs)).
    + rewrite Qplus_0_l. exact IH.
    + apply Qplus_le_compat.
      * apply Qle_0_sq.
      * apply Qle_refl.
Qed.

(* 非负乘法保非负 *)
Lemma Qle_mult_nonneg : forall x y : Q, Qle 0 x -> Qle 0 y -> Qle 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply (Qle_trans _ (0 * y)).
  - apply qeq_le. ring.
  - apply (Qmult_le_compat_r 0 x y); assumption.
Qed.

(* ========== Lagrange 交叉项（配方的逐项非负块） ==============
   x²·Σv² − 2xy·Σuv + y²·Σu² = Σ_pairs (x·v − y·u)² + 未配对余项·y²/x²
   ≥ 0（列表不等长时余项贡献平方项，仍非负——归纳同时覆盖）。 *)
Lemma crossQ : forall (xs ys : list Q) (x y : Q),
  Qle 0 (x * x * sqlQ ys - 2 * x * y * dotpQ xs ys + y * y * sqlQ xs).
Proof.
  induction xs as [| u us IH]; intros ys x y.
  - destruct ys as [| v vs].
    + (* 双空：恒等式 0 *)
      apply qeq_le. simpl. ring.
    + (* xs 空：x²·sqlQ(v::vs) ≥ 0 *)
      apply (Qle_trans _ (x * x * sqlQ (v :: vs))).
      * apply Qle_mult_nonneg.
        -- apply Qle_0_sq.
        -- apply Qle_0_sqlQ.
      * apply qeq_le. simpl. ring.
  - destruct ys as [| v vs].
    + (* ys 空：y²·sqlQ(u::us) ≥ 0 *)
      apply (Qle_trans _ (y * y * sqlQ (u :: us))).
      * apply Qle_mult_nonneg.
        -- apply Qle_0_sq.
        -- apply Qle_0_sqlQ.
      * apply qeq_le. simpl. ring.
    + (* 双 cons：(xv − yu)² + 归纳余块 *)
      apply (Qle_trans _ ((x * v - y * u) * (x * v - y * u)
                          + (x * x * sqlQ vs - 2 * x * y * dotpQ us vs
                             + y * y * sqlQ us))).
      * apply (Qle_trans _ (0 + (x * x * sqlQ vs
                                  - 2 * x * y * dotpQ us vs + y * y * sqlQ us))).
        -- rewrite Qplus_0_l. exact (IH vs x y).
        -- assert (Hq : Qle 0 ((x * v - y * u) * (x * v - y * u)))
             by apply Qle_0_sq.
           assert (Hr : Qle (x * x * sqlQ vs
                             - 2 * x * y * dotpQ us vs + y * y * sqlQ us)
                            (x * x * sqlQ vs
                             - 2 * x * y * dotpQ us vs + y * y * sqlQ us))
             by apply Qle_refl.
           exact (Qplus_le_compat 0 ((x * v - y * u) * (x * v - y * u))
                    _ _ Hq Hr).
      * apply qeq_le. simpl. ring.
Qed.

(* ========== Q 层有限和 Cauchy–Schwarz ======================== *)
Lemma cs_Q : forall (a b : list Q),
  Qle (dotpQ a b * dotpQ a b) (sqlQ a * sqlQ b).
Proof.
  induction a as [| x xs IHa]; intro b.
  - (* a 空：dotpQ = 0 *)
    cbn [dotpQ sqlQ]. rewrite !Qmult_0_l. apply Qle_refl.
  - destruct b as [| y ys].
    + (* b 空：dotpQ = 0 *)
      cbn [dotpQ sqlQ]. rewrite !Qmult_0_r. apply Qle_refl.
    + (* cons-cons：展开 + 配方
         (x²+A)(y²+B) − (xy+C)² = (x²B − 2xyC + y²A) + (AB − C²) ≥ 0 *)
      cbn [dotpQ sqlQ].
      assert (Hcs : Qle (dotpQ xs ys * dotpQ xs ys) (sqlQ xs * sqlQ ys))
        by apply IHa.
      assert (Hcross : Qle 0 (x * x * sqlQ ys - 2 * x * y * dotpQ xs ys
                              + y * y * sqlQ xs))
        by (apply crossQ).
      set (C := dotpQ xs ys). set (A := sqlQ xs). set (B := sqlQ ys).
      assert (Hstep : Qle (2 * x * y * C) (x * x * B + y * y * A)).
      { apply (Qle_trans _ (2 * x * y * C + 0)).
        - apply qeq_le. ring.
        - apply (Qle_trans _ (2 * x * y * C + (x * x * B - 2 * x * y * C
                                               + y * y * A))).
          + apply (Qplus_le_compat (2 * x * y * C) (2 * x * y * C) 0
                     (x * x * B - 2 * x * y * C + y * y * A));
               [apply Qle_refl | exact Hcross].
          + apply qeq_le. ring. }
      (* 主链：(xy+C)² ≤ x²y² + 2xyC + C² ≤ x²y² + (x²B+y²A) + C²
              ≤ x²y² + (x²B+y²A) + AB == (x²+A)(y²+B) *)
      apply (Qle_trans _ (x * x * y * y + 2 * x * y * C + C * C)).
      * apply qeq_le. ring.
      * apply (Qle_trans _ (x * x * y * y + (x * x * B + y * y * A) + C * C)).
        -- apply (Qplus_le_compat (x * x * y * y + 2 * x * y * C)
                     (x * x * y * y + (x * x * B + y * y * A)) (C * C) (C * C)).
           ++ apply (Qplus_le_compat (x * x * y * y) (x * x * y * y)
                       (2 * x * y * C) (x * x * B + y * y * A));
                [apply Qle_refl | exact Hstep].
           ++ apply Qle_refl.
        -- apply (Qle_trans _ (x * x * y * y + (x * x * B + y * y * A) + A * B)).
           ++ apply (Qplus_le_compat
                       (x * x * y * y + (x * x * B + y * y * A))
                       (x * x * y * y + (x * x * B + y * y * A))
                       (C * C) (A * B));
                [apply Qle_refl | exact Hcs].
           ++ apply qeq_le. ring.
Qed.

(* ========== 逐点投影（Real 层 → Q 层副本） =================== *)

Lemma sql_proj : forall (a : list Real) (k : nat),
  projT1 (sql a) k == sqlQ (map (fun x : Real => projT1 x k) a).
Proof.
  induction a as [| x xs IH]; intro k.
  - reflexivity.
  - cbn [sql]. rewrite real_plus_proj, real_mult_proj, IH. reflexivity.
Qed.

Lemma dotp_proj : forall (a b : list Real) (k : nat),
  projT1 (dotp a b) k
    == dotpQ (map (fun x : Real => projT1 x k) a)
             (map (fun y : Real => projT1 y k) b).
Proof.
  induction a as [| x xs IH]; intro b; intro k.
  - reflexivity.
  - destruct b as [| y ys].
    + reflexivity.
    + cbn [dotp]. rewrite real_plus_proj, real_mult_proj, IH. reflexivity.
Qed.

(* ========== Real 层主定理（eps 版有限和 Cauchy–Schwarz） ======
   关键观察：gap_n := (sql a)_n·(sql b)_n − (dotp a b)_n² ≥ 0 对**每个**
   指标 n 逐点成立（纯 Q 层 cs_Q，无需分支/判别式/除法）。故
   (AA·BB + eps)_n − (AB²)_n = gap_n + eps_n ≥ eps_n > e1（最终一致下界），
   real_lt 见证一步构造（e1 := eps 正性见证，N1 := 其模数）。 *)

Theorem real_cauchy_schwarz_lt :
  forall (a b : list Real) (eps : Real),
    real_lt real_zero eps ->
    real_lt (real_mult (dotp a b) (dotp a b))
            (real_plus (real_mult (sql a) (sql b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e1 [Hpos1 [N1 HN1]]].
  exists e1. split.
  - exact Hpos1.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
    (* 逐点投影展开：差 = (sql a)_n·(sql b)_n + eps_n − (dotp a b)_n² *)
    rewrite real_plus_proj, !real_mult_proj.
    rewrite (sql_proj a n), (sql_proj b n), (dotp_proj a b n).
    set (A := sqlQ (map (fun x : Real => projT1 x n) a)).
    set (B := sqlQ (map (fun x : Real => projT1 x n) b)).
    set (C := dotpQ (map (fun x : Real => projT1 x n) a)
                    (map (fun x : Real => projT1 x n) b)).
    (* eps 正性下界：e1 < eps_n *)
    assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
    assert (Hep : Qlt e1 (projT1 eps n)).
    { pose proof (HN1 n Hn) as Ht.
      apply QltT_to_Qlt in Ht.
      assert (Hzr : projT1 eps n - projT1 real_zero n == projT1 eps n).
      { rewrite Hz0. ring. }
      rewrite Hzr in Ht.
      exact Ht. }
    (* C-S 间隙逐点非负 *)
    assert (Hgap : Qle 0 (A * B - C * C)).
    { apply (Qle_trans _ (C * C - C * C)).
      - apply qeq_le. ring.
      - assert (Hcs := cs_Q (map (fun x : Real => projT1 x n) a)
                            (map (fun x : Real => projT1 x n) b)).
        unfold Qminus.
        exact (Qplus_le_compat (C * C) (A * B) (- (C * C)) (- (C * C))
                 Hcs (Qle_refl _)). }
    (* 合成：e1 < eps_n ≤ gap_n + eps_n = (AA·BB + eps)_n − (AB²)_n *)
    apply (Qlt_le_trans e1 (projT1 eps n)).
    + exact Hep.
    + apply (Qle_trans _ (0 + projT1 eps n)).
      * apply qeq_le. ring.
      * apply (Qle_trans _ ((A * B - C * C) + projT1 eps n)).
        -- exact (Qplus_le_compat 0 (A * B - C * C)
                    (projT1 eps n) (projT1 eps n) Hgap (Qle_refl _)).
        -- apply qeq_le. ring.
Qed.

(* ========== CS3：有限和 Cauchy–Schwarz（eps 版，real_le） ===== *)

Theorem real_cauchy_schwarz :
  forall (a b : list Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_mult (dotp a b) (dotp a b))
            (real_plus (real_mult (sql a) (sql b)) eps).
Proof.
  intros a b eps Heps.
  exact (inl (real_cauchy_schwarz_lt a b eps Heps)).
Qed.

(*
   任务原稿字面目标 real_le (AA·BB) (AB² + eps)（任意 eps>0）是假命题：
   反例 a=[1,0], b=[0,1]：AA·BB = 1，AB = 0，取 eps = 1/2 得"1 ≤ 1/2"。
   以下构造性证明 Not (...)，杜绝任何对该方向的误用。 *)

Definition cs_point_a : list Real := [real_const 1; real_zero].
Definition cs_point_b : list Real := [real_zero; real_const 1].

Lemma sql_pt_a_one : forall n : nat, projT1 (sql cs_point_a) n == 1.
Proof.
  intro n. unfold cs_point_a. cbn [sql].
  repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
  rewrite !real_const_proj.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

Lemma sql_pt_b_one : forall n : nat, projT1 (sql cs_point_b) n == 1.
Proof.
  intro n. unfold cs_point_b. cbn [sql].
  repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
  rewrite !real_const_proj.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

Lemma dotp_pt_zero : forall n : nat,
  projT1 (dotp cs_point_a cs_point_b) n == 0.
Proof.
  intro n. unfold cs_point_a, cs_point_b. cbn [dotp].
  repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
  rewrite !real_const_proj.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

Lemma pt_sql_eq :
  real_eq (real_mult (sql cs_point_a) (sql cs_point_b)) (real_const 1).
Proof.
  apply (RealSetoid.real_eq_mult_compat
           (sql cs_point_a) (sql cs_point_b) (real_const 1) (real_const 1)).
  - apply real_eq_of_zero_diff. intro n.
    rewrite sql_pt_a_one. rewrite real_const_proj. ring.
  - apply real_eq_of_zero_diff. intro n.
    rewrite sql_pt_b_one. rewrite real_const_proj. ring.
Qed.

Lemma pt_rhs_eq :
  real_eq (real_plus (real_mult (dotp cs_point_a cs_point_b)
                                  (dotp cs_point_a cs_point_b))
                     (real_const (1/2)%Q))
          (real_const (1/2)%Q).
Proof.
  assert (Hd0 : real_eq (dotp cs_point_a cs_point_b) (real_const 0)).
  { apply real_eq_of_zero_diff. intro n.
    rewrite dotp_pt_zero. rewrite real_const_proj. ring. }
  apply (RealSetoid.real_eq_plus_compat
           (real_mult (dotp cs_point_a cs_point_b)
                      (dotp cs_point_a cs_point_b))
           (real_const (1/2)%Q) (real_const 0) (real_const (1/2)%Q)).
  - exact (RealSetoid.real_eq_mult_compat (dotp cs_point_a cs_point_b)
             (dotp cs_point_a cs_point_b) (real_const 0) (real_const 0)
             Hd0 Hd0).
  - apply real_eq_refl.
Qed.

Lemma real_const_half_pos : real_lt real_zero (real_const (1/2)%Q).
Proof.
  exists (1/4)%Q. split.
  - exact (Qlt_to_QltT 0 (1/4)%Q (proj2 (Qlt_alt 0 (1/4)%Q) eq_refl)).
  - exists 0%nat. intros n _.
    apply Qlt_to_QltT.
    setoid_replace (projT1 (real_const (1/2)%Q) n - projT1 real_zero n)
      with (1/2)%Q.
    + exact (proj2 (Qlt_alt (1/4)%Q (1/2)%Q) eq_refl).
    + rewrite real_const_proj.
      change (projT1 real_zero n) with 0%Q.
      ring.
Qed.

Theorem real_cauchy_schwarz_reversed_false :
  Not (forall (a b : list Real) (eps : Real),
        real_lt real_zero eps ->
        real_le (real_mult (sql a) (sql b))
                (real_plus (real_mult (dotp a b) (dotp a b)) eps)).
Proof.
  intro H.
  assert (Hbad : real_le (real_const 1) (real_const (1/2)%Q)).
  { assert (Hspec := H cs_point_a cs_point_b (real_const (1/2)%Q)
                       real_const_half_pos).
    exact (real_le_trans (real_const 1)
             (real_mult (sql cs_point_a) (sql cs_point_b))
             (real_plus (real_mult (dotp cs_point_a cs_point_b)
                                   (dotp cs_point_a cs_point_b))
                        (real_const (1/2)%Q))
             (inr (real_eq_sym (real_const 1)
                    (real_mult (sql cs_point_a) (sql cs_point_b))
                    pt_sql_eq))
             (real_le_trans (real_mult (sql cs_point_a) (sql cs_point_b))
                (real_plus (real_mult (dotp cs_point_a cs_point_b)
                                      (dotp cs_point_a cs_point_b))
                           (real_const (1/2)%Q))
                (real_const (1/2)%Q)
                Hspec (inr pt_rhs_eq))). }
  destruct Hbad as [Hlt | Heq].
  - (* real_lt 1 (1/2)：与见证正性 e > 0 矛盾 *)
    destruct Hlt as [e [Hepos [N HN]]].
    specialize (HN N (NatLe_lift N N (le_n N))).
    apply QltT_to_Qlt in HN.
    assert (Hd : projT1 (real_const (1/2)%Q) N - projT1 (real_const 1) N
                 == ((-1)#2)%Q).
    { rewrite !real_const_proj. vm_compute. reflexivity. }
    rewrite Hd in HN.
    exfalso.
    pose proof (Qlt_trans 0 e ((-1)#2)%Q (QltT_to_Qlt 0 e Hepos) HN) as Hcontra.
    vm_compute in Hcontra.
    discriminate Hcontra.
  - (* real_eq 1 (1/2)：取 eps := 1/4，|1 − 1/2| = 1/2 不小于 1/4 *)
    specialize (Heq (1/4)%Q
                  (Qlt_to_QltT 0 (1/4)%Q (proj2 (Qlt_alt 0 (1/4)%Q) eq_refl))).
    destruct Heq as [M HM].
    specialize (HM M (NatLe_lift M M (le_n M))).
    unfold QltT in HM.
    vm_compute in HM.
    inversion HM.
Qed.

(* ========== G3：提取检验 ====================================== *)

Set Warnings "-extraction-opaque-accessed".

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions real_cauchy_schwarz.
