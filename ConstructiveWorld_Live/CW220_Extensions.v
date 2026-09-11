(* ===================================================================== *)
(* CW220_Extensions.v — 220 版扩展层 v3（信任缓存分发形态）                  *)
(*   基座：CW_ConstructiveWorld_219（vo 信任缓存）                          *)
(*   34 件合并区；8 件 Module 隔离（根同名声明碰撞）；消费席 Import 注入      *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.

(* ---------- UpCS ---------- *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring QArith.Qabs.
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
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
(* 方向勘误（重要）：任务原稿目标                                 *)
(*     real_le (AA·BB) (AB² + eps)（对任意 eps > 0）              *)
(*   是**假命题**（反例 a=[1,0], b=[0,1]：AA·BB = 1 > eps 可取    *)
(*   1/2，则 1 ≤ 0 + 1/2 不成立）；且与原稿自己的证明路线结论      *)
(*   "即 (AB)² ≤ AA·BB" 相矛盾。本文件按 C-S 的真实方向交付        *)
(*   real_le (AB²) (AA·BB + eps)，并在文末给出原方向的形式化反驳    *)
(*   （Not (...)，非平凡反例构造）。                              *)
(*                                                              *)
(* 红线：纯构造性；Set 层语句（real_lt/real_le Or 编码/real_eq）；  *)
(*   零公理、零搁置证明、零中止、零经典逻辑；全部 Qed 闭合；可提取。 *)
(* ============================================================ *)

Import ListNotations.

Open Scope Q_scope.

(* ========== CS1：内积（逐项相乘有限和） ====================== *)
Fixpoint cwe_dotp (a b : list Real) : Real :=
  match a, b with
  | x :: xs, y :: ys => real_plus (real_mult x y) (cwe_dotp xs ys)
  | _, _ => real_zero
  end.

(* ========== CS2：平方和 ====================================== *)
Fixpoint cwe_sql (a : list Real) : Real :=
  match a with
  | nil => real_zero
  | x :: rest => real_plus (real_mult x x) (cwe_sql rest)
  end.

(* ========== Q 层镜像（逐点求值目标） ========================= *)
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

(* ========== 逐点投影（Real 层 → Q 层镜像） =================== *)

Lemma sql_proj : forall (a : list Real) (k : nat),
  projT1 (cwe_sql a) k == sqlQ (map (fun x : Real => projT1 x k) a).
Proof.
  induction a as [| x xs IH]; intro k.
  - reflexivity.
  - cbn [cwe_sql]. rewrite real_plus_proj, real_mult_proj, IH. reflexivity.
Qed.

Lemma dotp_proj : forall (a b : list Real) (k : nat),
  projT1 (cwe_dotp a b) k
    == dotpQ (map (fun x : Real => projT1 x k) a)
             (map (fun y : Real => projT1 y k) b).
Proof.
  induction a as [| x xs IH]; intro b; intro k.
  - reflexivity.
  - destruct b as [| y ys].
    + reflexivity.
    + cbn [cwe_dotp]. rewrite real_plus_proj, real_mult_proj, IH. reflexivity.
Qed.

(* ========== Real 层主定理（eps 版有限和 Cauchy–Schwarz） ======
   关键观察：gap_n := (cwe_sql a)_n·(cwe_sql b)_n − (cwe_dotp a b)_n² ≥ 0 对**每个**
   指标 n 逐点成立（纯 Q 层 cs_Q，无需分支/判别式/除法）。故
   (AA·BB + eps)_n − (AB²)_n = gap_n + eps_n ≥ eps_n > e1（最终一致下界），
   real_lt 见证一步构造（e1 := eps 正性见证，N1 := 其模数）。 *)

Theorem real_cauchy_schwarz_lt :
  forall (a b : list Real) (eps : Real),
    real_lt real_zero eps ->
    real_lt (real_mult (cwe_dotp a b) (cwe_dotp a b))
            (real_plus (real_mult (cwe_sql a) (cwe_sql b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e1 [Hpos1 [N1 HN1]]].
  exists e1. split.
  - exact Hpos1.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
    (* 逐点投影展开：差 = (cwe_sql a)_n·(cwe_sql b)_n + eps_n − (cwe_dotp a b)_n² *)
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
    real_le (real_mult (cwe_dotp a b) (cwe_dotp a b))
            (real_plus (real_mult (cwe_sql a) (cwe_sql b)) eps).
Proof.
  intros a b eps Heps.
  exact (inl (real_cauchy_schwarz_lt a b eps Heps)).
Qed.

(* ========== 方向勘误的形式化反驳 ==============================
   任务原稿字面目标 real_le (AA·BB) (AB² + eps)（任意 eps>0）是假命题：
   反例 a=[1,0], b=[0,1]：AA·BB = 1，AB = 0，取 eps = 1/2 得"1 ≤ 1/2"。
   以下构造性证明 Not (...)，杜绝任何对该方向的误用。 *)

Definition cs_point_a : list Real := [real_const 1; real_zero].
Definition cs_point_b : list Real := [real_zero; real_const 1].

Lemma sql_pt_a_one : forall n : nat, projT1 (cwe_sql cs_point_a) n == 1.
Proof.
  intro n. unfold cs_point_a. cbn [cwe_sql].
  repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
  rewrite !real_const_proj.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

Lemma sql_pt_b_one : forall n : nat, projT1 (cwe_sql cs_point_b) n == 1.
Proof.
  intro n. unfold cs_point_b. cbn [cwe_sql].
  repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
  rewrite !real_const_proj.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

Lemma dotp_pt_zero : forall n : nat,
  projT1 (cwe_dotp cs_point_a cs_point_b) n == 0.
Proof.
  intro n. unfold cs_point_a, cs_point_b. cbn [cwe_dotp].
  repeat rewrite real_plus_proj. repeat rewrite real_mult_proj.
  rewrite !real_const_proj.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

Lemma pt_sql_eq :
  real_eq (real_mult (cwe_sql cs_point_a) (cwe_sql cs_point_b)) (real_const 1).
Proof.
  apply (RealSetoid.real_eq_mult_compat
           (cwe_sql cs_point_a) (cwe_sql cs_point_b) (real_const 1) (real_const 1)).
  - apply real_eq_of_zero_diff. intro n.
    rewrite sql_pt_a_one. rewrite real_const_proj. ring.
  - apply real_eq_of_zero_diff. intro n.
    rewrite sql_pt_b_one. rewrite real_const_proj. ring.
Qed.

Lemma pt_rhs_eq :
  real_eq (real_plus (real_mult (cwe_dotp cs_point_a cs_point_b)
                                  (cwe_dotp cs_point_a cs_point_b))
                     (real_const (1/2)%Q))
          (real_const (1/2)%Q).
Proof.
  assert (Hd0 : real_eq (cwe_dotp cs_point_a cs_point_b) (real_const 0)).
  { apply real_eq_of_zero_diff. intro n.
    rewrite dotp_pt_zero. rewrite real_const_proj. ring. }
  apply (RealSetoid.real_eq_plus_compat
           (real_mult (cwe_dotp cs_point_a cs_point_b)
                      (cwe_dotp cs_point_a cs_point_b))
           (real_const (1/2)%Q) (real_const 0) (real_const (1/2)%Q)).
  - exact (RealSetoid.real_eq_mult_compat (cwe_dotp cs_point_a cs_point_b)
             (cwe_dotp cs_point_a cs_point_b) (real_const 0) (real_const 0)
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
        real_le (real_mult (cwe_sql a) (cwe_sql b))
                (real_plus (real_mult (cwe_dotp a b) (cwe_dotp a b)) eps)).
Proof.
  intro H.
  assert (Hbad : real_le (real_const 1) (real_const (1/2)%Q)).
  { assert (Hspec := H cs_point_a cs_point_b (real_const (1/2)%Q)
                       real_const_half_pos).
    exact (real_le_trans (real_const 1)
             (real_mult (cwe_sql cs_point_a) (cwe_sql cs_point_b))
             (real_plus (real_mult (cwe_dotp cs_point_a cs_point_b)
                                   (cwe_dotp cs_point_a cs_point_b))
                        (real_const (1/2)%Q))
             (inr (real_eq_sym (real_const 1)
                    (real_mult (cwe_sql cs_point_a) (cwe_sql cs_point_b))
                    pt_sql_eq))
             (real_le_trans (real_mult (cwe_sql cs_point_a) (cwe_sql cs_point_b))
                (real_plus (real_mult (cwe_dotp cs_point_a cs_point_b)
                                      (cwe_dotp cs_point_a cs_point_b))
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

(* ========== G3：提取探针 ====================================== *)

Set Warnings "-extraction-opaque-accessed".

Extraction "upcs.ml" cwe_dotp cwe_sql cs_Q crossQ real_cauchy_schwarz real_cauchy_schwarz_lt.

(* ---------- UpHlogZ ---------- *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* ============================================================ *)
(* UpHlogZ.v —— 根内 KLProjection 主定理 HlogZ 前提的 Real 层总放电   *)
(*                                                              *)
(* 目标：projected_distribution_minimizes_kl（KLProjection.v L189）  *)
(* 的显式前件 HlogZ : le (log Z_aud) zero 在 Real 层总是成立：        *)
(*   Z_aud ≤ 1（Z_aud_le_one，根内已证）                           *)
(*   ⟹ log Z_aud ≤ log 1 = 0                                      *)
(*     （log 单调 le 版 = UpLogMono.real_log_le_mono；              *)
(*       log 1 == 0 = real_log_one，根内已证）。                    *)
(*                                                              *)
(* 交付清单：                                                      *)
(*   hlogz_discharge       —— 主放电：0 < Z ≤ 1 ⟹ log Z ≤ 0        *)
(*   hlogz_discharge_full  —— 同型对齐版（走 UpLogMono 直用形态）    *)
(*   hlogz_strict          —— 严格版：0 < Z < 1 ⟹ log Z < 0         *)
(*                            （过滤器确实拦截了质量）               *)
(*   hlogz_opp_nonneg      —— KL 尾项形态：0 ≤ opp (log Z)          *)
(*                            （主定理证明中 opp_le_compat 的直接输入）*)
(*                                                              *)
(* 全部 Real 层、Set 层语句（real_lt / real_le / real_eq，Or 编码）、 *)
(* 纯构造、全 Qed 闭合、可提取。                                    *)
(* ============================================================ *)


(* ================================================================ *)
(* 主交付 1：HlogZ 放电（log 单调 le 版直推）                          *)
(*   论证：0 < Za、Za ≤ 1 ⟹ real_log Za ≤ real_log 1 == 0。           *)
(*   real_log_le_mono : real_le a b -> real_le (log a) (log b)       *)
(*   （a b 皆正前提由 HZa 与 real_lt_zero_one 供给）。                 *)
(* ================================================================ *)
Theorem hlogz_discharge :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  (* 经中项 real_log 1 的 le 链合成 *)
  apply (real_le_trans _ (real_log real_one Hone) _).
  - (* 单调 le 版：Za ≤ 1 ⟹ log Za ≤ log 1 *)
    exact (real_log_le_mono Za real_one HZa Hone HZa1).
  - (* log 1 == 0 经 eq → le 桥（inr 支）升 le *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* ================================================================ *)
(* 主交付 2：HlogZ 放电完整版（与 KLProjection 前件对齐）               *)
(*   同型语句，走 UpLogMono 直用形态 real_log_le_zero_of_le_one，      *)
(*   双路互证（单调链合成 / 直用形态殊途同归）。                        *)
(* ================================================================ *)
Theorem hlogz_discharge_full :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  exact (real_log_le_zero_of_le_one Za HZa HZa1).
Qed.

(* ================================================================ *)
(* 附加交付 1：严格版——过滤器确实拦截了质量                            *)
(*   0 < Za < 1 ⟹ log Za < log 1 = 0（lt 严格链）。                   *)
(*   real_log_lt_mono 论 cw_log；real_log 定义性展开（:= cw_log）后    *)
(*   逐项对接，尾端经 real_lt_eq_lt 把 log 1 换成 0。                  *)
(* ================================================================ *)
Theorem hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - (* 严格单调：Za < 1 ⟹ cw_log Za < cw_log 1 *)
    unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - (* cw_log 1 == 0 *)
    exact (real_log_one Hone).
Qed.

(* ================================================================ *)
(* 附加交付 2：KL 尾项形态——0 ≤ opp (log Z)                           *)
(*   主定理证明里「尾项 T == opp (log Z_aud) ≥ 0」的直接 Real 层供给：  *)
(*   log Z ≤ 0 经 opp 反变（real_opp_le_compat）→ opp 0 ≤ opp (log Z)，*)
(*   再用 opp 0 == 0 的 eq → le 桥（inl 支？否，inr 支）合成。          *)
(* ================================================================ *)
Theorem hlogz_opp_nonneg :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le real_zero (real_opp (real_log Za HZa)).
Proof.
  intros Za HZa HZa1.
  apply (real_le_trans _ (real_opp real_zero) _).
  - (* 0 ≤ opp 0：eq 对称后升 le *)
    exact (real_eq_le_bridge real_zero (real_opp real_zero)
             (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)).
  - (* opp 0 ≤ opp (log Z)：反变 + 主交付 1 *)
    exact (real_opp_le_compat (real_log Za HZa) real_zero
             (hlogz_discharge Za HZa HZa1)).
Qed.

(* 提取探针（Warning 消音：透明度旁路访问清单提示，与 UpGRPO 同法） *)
Set Warnings "-extraction-opaque-accessed".

Extraction "uphlogz.ml" hlogz_discharge hlogz_strict hlogz_opp_nonneg.

(* ---------- UpDebtSqrtAbs ---------- *)
Module DebtSqrtAbs.
(* ============================================================ *)
(* UpDebtSqrtAbs.v —— 债务清理打包席（件 3，方案三 b+）          *)
(*   抽象 Id 系增强接口下任意非负 d 的构造性平方根见证：          *)
(*   把 Real 层 real_sqrt_exists（根 L96475）的 Or 分支证书      *)
(*   结构逐字镜像回 RealInterfaceEnhanced 接口泛型。             *)
(*                                                              *)
(*   语句（任务书模板）：                                        *)
(*     forall d, Or (lt zero d) (Id zero d) ->                  *)
(*       sigT (fun r => And (le zero r) (Id (mult r r) d))      *)
(*   证明核：                                                    *)
(*     左支 d>0：r := exp_neg(half·log_inv d)（half :=           *)
(*       inv_pos two，two := 1+1 正性经 plus_positive 组装），    *)
(*       r·r == d 链 = exp_neg_plus 反向 + distrib/mult 代数     *)
(*       （half+half == one）+ exp_neg_log_inv 右逆；            *)
(*     右支 d≡0：r := zero（mult_zero）。                        *)
(*                                                              *)
(*   诚实接口说明：接口的 le 是不透明字段，库内仅有 Or→le 单向   *)
(*   （lt_le_iff），故前件取 Or 形态——这正是 real_le 的定义体    *)
(*   （real_le x y := Or (real_lt x y) (real_eq x y)），与 Real  *)
(*   层 real_sqrt_exists 的可消费前提逐字同构；le 形态前提在接口 *)
(*   内无法分解（无 le→Or 字段），不硬凑。                       *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（lt/le/Id/sigT/And）；*)
(*   全部 Qed 收口。                                             *)
(* ============================================================ *)


Section SqrtAbstract.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 平方维数见证（镜像根内 sqrt_witness）：r·r == d *)
Definition cwe_sqrt_witness (d r : R) : Set := Id (mult r r) d.

(* two := 1+1（字面 2）；two > 0（plus_positive × one_pos 组装） *)
Definition two_abs : R := plus one one.
Lemma two_abs_pos : lt zero two_abs.
Proof.
  exact (plus_positive one one one_pos one_pos).
Qed.

(* half := inv(two)；half + half == one
   链：half·two == one（inv_pos_correct，经 mult_comm），
       half·two == half·(1+1) == half·1 + half·1 == half + half
       （distrib + mult_one × 2）。 *)
Definition half_abs : R := inv_pos two_abs two_abs_pos.
Lemma half_plus_half : Id (plus half_abs half_abs) one.
Proof.
  assert (Hd : Id (mult half_abs two_abs) one)
    by exact (id_trans (mult_comm half_abs two_abs)
                       (inv_pos_correct two_abs two_abs_pos)).
  assert (Hsplit : Id (mult half_abs two_abs) (plus half_abs half_abs))
    by exact (id_trans (distrib half_abs one one)
                       (id_cong2 (fun a b => plus a b)
                                 (mult_one half_abs) (mult_one half_abs))).
  exact (id_trans (id_sym Hsplit) Hd).
Qed.

(* Or 前件即 le 的构造性内容（接口单向 lt_le_iff 的记录） *)
Lemma sqrt_premise_le_intro : forall d : R, Or (lt zero d) (Id zero d) -> le zero d.
Proof.
  intros d H. apply lt_le_iff. exact H.
Qed.

(* ---- 旗舰（件 3）：抽象 Id 层任意非负 d 的平方根见证 ----
   左支（d > 0，正间隙证书）：r := exp_neg(half·log_inv d)。
     r·r == d：exp(h)·exp(h) == exp(h+h)（exp_neg_plus 反向）
       == exp(log_inv d)（h+h == half·L+half·L == half·(L+L)
       == one·L == L，其中 half+half == one）
       == d（exp_neg_log_inv 右逆）。
     r > 0：exp_neg_pos + lt_le_iff。
   右支（d ≡ 0，Id 证书）：r := zero；0 ≤ 0（le_refl）；
     0·0 == 0（mult_zero）== d（Hdeq）。 *)
Theorem sqrt_witness_exists_abstract :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (Id (mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - (* 情形①：d > 0。r := exp(half·log d)。 *)
    exists (exp_neg (mult half_abs (log_inv d))).
    split.
    + (* r > 0：exp 恒正（le 左支 = lt 经 lt_le_iff） *)
      exact (lt_le_iff zero (exp_neg (mult half_abs (log_inv d)))
                        (inl (exp_neg_pos (mult half_abs (log_inv d))))).
    + (* r·r == d：三分链 exp(h)·exp(h) == exp(h+h) == exp(log d) == d *)
      assert (Hinner : Id (plus (mult half_abs (log_inv d))
                                (mult half_abs (log_inv d)))
                          (log_inv d)).
      { exact (id_trans
                (id_trans
                  (id_cong2 (fun a b => plus a b)
                            (mult_comm half_abs (log_inv d))
                            (mult_comm half_abs (log_inv d)))
                  (id_trans (id_sym (distrib (log_inv d) half_abs half_abs))
                            (mult_comm (log_inv d) (plus half_abs half_abs))))
                (id_trans
                  (id_cong (fun x => mult x (log_inv d)) half_plus_half)
                  (id_trans (mult_comm one (log_inv d))
                            (mult_one (log_inv d))))). }
      exact (id_trans
              (id_sym (exp_neg_plus (mult half_abs (log_inv d))
                                    (mult half_abs (log_inv d))))
              (id_trans (id_cong (fun x => exp_neg x) Hinner)
                        (exp_neg_log_inv d))).
  - (* 情形②：d ≡ 0。r := zero。 *)
    exists zero.
    split.
    + (* 0 ≤ 0：自反 *)
      apply le_refl.
    + (* 0·0 == 0 == d *)
      exact (id_trans (mult_zero zero) Hdeq).
Qed.

(* 见证形态重述（cwe_sqrt_witness 命名式） *)
Lemma sqrt_witness_exists_abstract_witness :
  forall d : R, Or (lt zero d) (Id zero d) ->
  sigT (fun r : R => And (le zero r) (cwe_sqrt_witness d r)).
Proof.
  intros d H.
  exact (sqrt_witness_exists_abstract d H).
Qed.

(* 实例（机器可检查的健全性检查）：1 的抽象平方根可构造——
   r := exp(half·log_inv 1)，r ≥ 0 且 r·r == 1（镜像 real_sqrt_one）。 *)
Lemma sqrt_one_abstract :
  sigT (fun r : R => And (le zero r) (Id (mult r r) one)).
Proof.
  exact (sqrt_witness_exists_abstract one (inl one_pos)).
Qed.

End SqrtAbstract.
End DebtSqrtAbs.

(* ---------- UpDebtDual ---------- *)
(* ============================================================ *)
(* UpDebtDual.v —— 债务清理打包席（件 2，方案三 b）              *)
(*   缩放-温度对偶族 Real 层：抽象层 scale_temp_duality           *)
(*   （CW214KL_scan L28515–28529）与配套缩放族（L28440–28543）   *)
(*   的 Real 层镜像。                                            *)
(*                                                              *)
(*   定义族：                                                    *)
(*     real_softmax_scaled c z s      := e^{c·z_s}/Σ e^{c·z}     *)
(*     real_softmax_temp_param T z s  := e^{z/T}/Σ e^{z/T}       *)
(*   主定理：                                                    *)
(*     real_scale_temp_duality：∀c>0,                            *)
(*       real_softmax_scaled (1/c) == real_softmax_temp_param c  *)
(*   配套：缩放族正性/归一化 + real_scale_inv_T_eq_softmax_temp  *)
(*   （1/T 缩放族 == 库式温度化 softmax，配分定义性相等经        *)
(*   real_inv_pos_ext——纯恒等链）。                              *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（real_lt/real_eq/     *)
(*   sigT/And）；全部 Qed 收口。                                  *)
(* ============================================================ *)


Section RealScaleDual.

(* 抽象状态空间（Real 层 Section 自声明，同 RealAttnMain 先例） *)
Variable S : Type.

(* 诚实接口：抽象 S 上的求和（Real 层可实例化；零公理） *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* ---- 缩放族：real_softmax_scaled ---- *)

(* 缩放配分函数：Z_c(z) := Σ_s e^{c·z_s}（c 任意实） *)
Definition real_partition_function_scaled (c : Real) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s))).

(* 缩放配分正性：exp 恒正 × sum_pos_preserved *)
Lemma real_partition_function_scaled_pos :
  forall (c : Real) (z : S -> Real), real_lt real_zero (real_partition_function_scaled c z).
Proof.
  intros c z.
  unfold real_partition_function_scaled, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* 缩放 softmax：sc(z; c)_s := e^{c·z_s}·inv(Z_c(z))（c 任意实） *)
Definition real_softmax_scaled (c : Real) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult c (z s)))
            (real_inv_pos (real_partition_function_scaled c z)
                          (real_partition_function_scaled_pos c z)).

(* 缩放族概率公理：正性（exp 恒正 × inv 正） *)
Theorem real_softmax_scaled_pos :
  forall (c : Real) (z : S -> Real) (s : S), real_lt real_zero (real_softmax_scaled c z s).
Proof.
  intros c z s.
  unfold real_softmax_scaled, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 缩放族概率公理：归一化 Σ_s sc(z;c)_s == 1
   链：逐 s 乘子交换（sum_ext + real_mult_comm）→ 线性提取
   （sum_linear）→ inv(Z_c)·Z_c == 1（real_inv_pos_correct）。 *)
Theorem real_softmax_scaled_normalized :
  forall (c : Real) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_scaled c z s)) real_one.
Proof.
  intros c z.
  unfold real_softmax_scaled.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult c (z s)))
                             (real_inv_pos (real_partition_function_scaled c z)
                                           (real_partition_function_scaled_pos c z))))
          (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                   (real_partition_function_scaled_pos c z))
                     (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
          real_one).
  - (* 1. 乘子交换后线性提取 *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult c (z s)))
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_scaled c z)
                                             (real_partition_function_scaled_pos c z))
                               (real_exp_pos_fn (real_mult c (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_c)·Z_c == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_sum_over_S (fun s => real_exp_pos_fn (real_mult c (z s)))))
            (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                     (real_partition_function_scaled_pos c z))
                       (real_partition_function_scaled c z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z))
                         (real_partition_function_scaled c z))
              (real_mult (real_partition_function_scaled c z)
                         (real_inv_pos (real_partition_function_scaled c z)
                                       (real_partition_function_scaled_pos c z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- 温度参数化族：(T0, HT0) 显式版 ---- *)

(* 温度参数化配分函数：Z_T0(z) := Σ_s e^{z_s/T0} *)
Definition real_partition_function_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s))).

(* 温度参数化配分正性 *)
Lemma real_partition_function_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_lt real_zero (real_partition_function_temp_param T0 HT0 z).
Proof.
  intros T0 HT0 z.
  unfold real_partition_function_temp_param, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* 温度参数化 softmax：e^{z_s/T0}·inv(Z_T0(z)) *)
Definition real_softmax_temp_param
  (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
            (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                          (real_partition_function_temp_param_pos T0 HT0 z)).

(* 温度参数化正性（配套） *)
Theorem real_softmax_temp_param_pos :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real) (s : S),
    real_lt real_zero (real_softmax_temp_param T0 HT0 z s).
Proof.
  intros T0 HT0 z s.
  unfold real_softmax_temp_param, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 温度参数化归一化（配套） *)
Theorem real_softmax_temp_param_normalized :
  forall (T0 : Real) (HT0 : real_lt real_zero T0) (z : S -> Real),
    real_eq (real_sum_over_S (fun s => real_softmax_temp_param T0 HT0 z s)) real_one.
Proof.
  intros T0 HT0 z.
  unfold real_softmax_temp_param.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                             (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                           (real_partition_function_temp_param_pos T0 HT0 z))))
          (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                   (real_partition_function_temp_param_pos T0 HT0 z))
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
          real_one).
  - apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                             (real_partition_function_temp_param_pos T0 HT0 z))
                               (real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - apply (real_eq_trans
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T0 HT0) (z s)))))
            (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                     (real_partition_function_temp_param_pos T0 HT0 z))
                       (real_partition_function_temp_param T0 HT0 z))
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z))
                         (real_partition_function_temp_param T0 HT0 z))
              (real_mult (real_partition_function_temp_param T0 HT0 z)
                         (real_inv_pos (real_partition_function_temp_param T0 HT0 z)
                                       (real_partition_function_temp_param_pos T0 HT0 z)))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- 主定理（件 2 核心）：缩放-温度对偶 ----
   ∀ c > 0：以 1/c 缩放 logits 的 softmax == 温度 c 的 softmax。
   unfold 后两侧首因子（分子 e^{(1/c)·z_s}）逐字相同，mult_compat
   refl 消去；配分函数定义性相等（两侧都 unfold 为同一 Σ）⟹
   real_inv_pos_ext + real_eq_refl。纯恒等链，零新公理。 *)
Theorem real_scale_temp_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_scaled (real_inv_pos c Hc) z s)
            (real_softmax_temp_param c Hc z s).
Proof.
  intros c Hc z s.
  unfold real_softmax_scaled, real_softmax_temp_param.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_exp_pos_fn (real_mult (real_inv_pos c Hc) (z s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos c Hc) z)
                        (real_partition_function_scaled_pos (real_inv_pos c Hc) z))
          (real_inv_pos (real_partition_function_temp_param c Hc z)
                        (real_partition_function_temp_param_pos c Hc z))
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos c Hc) z)
            (real_partition_function_temp_param c Hc z)
            (real_partition_function_scaled_pos (real_inv_pos c Hc) z)
            (real_partition_function_temp_param_pos c Hc z)
            (real_eq_refl _))).
Qed.

(* 反向对称：温度 c 的 softmax == 以 1/c 缩放的 softmax（real_eq_sym） *)
Lemma real_temp_is_scale_duality :
  forall (c : Real) (Hc : real_lt real_zero c) (z : S -> Real) (s : S),
    real_eq (real_softmax_temp_param c Hc z s)
            (real_softmax_scaled (real_inv_pos c Hc) z s).
Proof.
  intros c Hc z s.
  apply real_eq_sym.
  apply real_scale_temp_duality.
Qed.

(* ---- Section 温度版桥：1/T 缩放族 == 库式温度化 softmax ----
   库式 softmax_temp（L28104 型）的温度 T/配分 Z_T 为 Section
   变量显式定义（不带参数化前件）；此处重建该形态，并以
   real_inv_pos_ext + real_eq_refl 桥接（配分定义性相等）。 *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable z_logits : S -> Real.

(* 库式温度化配分（Section 温度形态） *)
Definition cwe_real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma cwe_real_partition_function_temp_pos : real_lt real_zero cwe_real_partition_function_temp.
Proof.
  unfold cwe_real_partition_function_temp, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* 库式温度化 softmax（Section 温度形态） *)
Definition cwe_real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos).

(* 桥（对偶引理 c := T 实例 + 配分定义性相等） *)
Lemma real_scale_inv_T_eq_softmax_temp :
  forall s : S,
    real_eq (real_softmax_scaled (real_inv_pos T T_pos) z_logits s)
            (cwe_real_softmax_temp s).
Proof.
  intro s.
  unfold real_softmax_scaled, cwe_real_softmax_temp.
  apply (RealSetoid.real_eq_mult_compat_adapt
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
          (real_inv_pos (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
                        (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits))
          (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos)
          (real_eq_refl _)
          (real_inv_pos_ext
            (real_partition_function_scaled (real_inv_pos T T_pos) z_logits)
            cwe_real_partition_function_temp
            (real_partition_function_scaled_pos (real_inv_pos T T_pos) z_logits)
            cwe_real_partition_function_temp_pos
            (real_eq_refl _))).
Qed.

End RealScaleDual.

(* ---------- UpEntropyGain ---------- *)
(* ============================================================
   UpEntropyGain.v —— 榜 A2：second_law_irreversible（根 L27796）
   从"假设搬运型平凡"升级为带定量增量的真定理。

   件 1  entropy_step_gain_lower：
     一步梯度上升 x' := x + η·g(x) 的熵增量定量下界
       entropy(x') − entropy(x) ≥ η·(1 − L·η)·g(x)²     （g(x) > 0）
   件 2  entropy_gain_positive：
     0 < η、0 < L、ηL < 1、g(x) > 0 ⟹ 0 < entropy(x') − entropy(x)
   件 3  second_law_quant（对照注记）：
     同条件下严格熵增 lt (entropy x) (entropy (dynamics x))——
     以"充分条件版定理"取代根 SecondLaw 区的
     Variable strict_entropy_increase 假设重述（旧件可退役）。

   纸笔推导（tangent 接口 + Lipschitz 实际形态）：
     (i)   切线（凹景观上界）在 x' 处取 y := x：
           e ≤ e' + g'·(x − x')，而 x − x' = −η·g
           ⟹ e' − e ≥ η·g·g'。
     (ii)  下界 g' ≥ (1 − Lη)·g 来自 Lipschitz 单边提取：
           g − g' ≤ |g − g'| ≤ L|x − x'| = Lη·g（g > 0 时 |x−x'| = ηg）。
           注意 strong_concavity(μ) 只给 g' ≤ (1−ημ)·g（上界），
           无法控制步长过大时的回落——曲率修正项的常数只能是 L。
     (iii) g > 0 两侧乘 (1−Lη)g ≥ g' 得 g·g' ≥ (1−Lη)g²
           ⟹ 增量 ≥ η(1−Lη)g²。
     数值 sanity（f = log, x = 2, η = 0.4, L = 2）：
           真增量 log(1.2) ≈ 0.182 ≥ 下界 0.4·(1−0.8)·0.25 = 0.02 ✓。
     正性条件是 ηL < 1 而非草案的 ημ < 1：μ ≤ L（Lipschitz 与强凹
           相容时）⟹ 1/L ≤ 1/μ，ημ < 1 控制不住过冲，诚实常数取 1/L。
     g(x) < 0 负支同界（|g| 收缩对称），但其提取需符号三分判定，
           构造性 Set 层不可达——如实降级为 g(x) > 0 单侧版。

   纪律：纯构造性 / Set 层 / 零未证缺口 / 零经典 / 语句零 Prop
        （lt/le 均接口 Set 字段；无 Not/Or 前提）/ 可提取 OCaml。
   诚实接口：entropy_tangent / gradient_lipschitz /
        dynamics_gradient_step 复刻根 ConvergenceCauchy 区同名
        Variable；abs_ge_value（le a (abs a)，与根 abs_ge_zero_id_cc
        同族的构造性有序域标准性质，Real 层可证）与
        lt_plus_compat_lt_le（根区同名 Variable 先例）为本区新增。
   ============================================================ *)

Section EntropyGainQuant.

Context {RI : RealInterfaceEnhanced}.

(* 解包 RealInterface 字段（同根 ConvergenceCauchy 先例） *)
Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
(* minus 保持根全局 Definition（minus a b := plus a (opp b)，定义性展开） *)

(* ===== 诚实接口（Variable 复刻根 ConvergenceCauchy 区） ===== *)
Variable entropy : R -> R.
Variable entropy_gradient : R -> R.
Variable dynamics : R -> R.
Variable eta : R.
Variable eta_pos : lt zero eta.
Variable dynamics_gradient_step : forall x : R,
  Id (dynamics x) (plus x (mult eta (entropy_gradient x))).
Variable L : R.
Variable L_pos : lt zero L.
Variable gradient_lipschitz : forall x y : R,
  le (abs (minus (entropy_gradient x) (entropy_gradient y)))
     (mult L (abs (minus x y))).
Variable entropy_tangent : forall x y : R,
  le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (minus y x))).
(* 新增诚实接口：|·| 的单边提取（le a (abs a)；根 abs_ge_zero_id_cc
   同族——le zero a -> |a| == a 的姊妹形态；构造性有序域标准性质，
   柯西实数模型可证，抽象层声明为接口字段，非经典公理） *)
Variable abs_ge_value : forall a : R, le a (abs a).
(* 混合 lt+le 加法保序（根 ConvergenceCauchy 区同名 Variable 先例） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ===== 基础代数（Root 全局层无此三件的手工链） ===== *)

(* 减法定义（minus 透明，定义性相等） *)
Lemma eg_minus_def : forall a b : R, Id (minus a b) (plus a (opp b)).
Proof. intros a b. apply id_refl. Qed.

(* 减法可逆：(a − b) + b == a *)
Lemma eg_minus_plus_cancel : forall a b : R,
  Id (plus (minus a b) b) a.
Proof.
  intros a b. unfold minus.
  apply (id_trans (id_sym (plus_assoc a (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_comm (opp b) b))).
  apply (id_trans (id_cong (fun z => plus a z) (plus_opp b))).
  apply (plus_zero a).
Qed.

(* K0 单步展开（差形式）：x' − x == η·g(x) *)
Lemma eg_step_diff : forall x : R,
  Id (minus (dynamics x) x) (mult eta (entropy_gradient x)).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus z (opp x)) (dynamics_gradient_step x))).
  apply (id_trans (id_sym (plus_assoc x (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (plus_comm (mult eta (entropy_gradient x)) (opp x)))).
  apply (id_trans (plus_assoc x (opp x) (mult eta (entropy_gradient x)))).
  apply (id_trans (id_cong (fun z => plus z (mult eta (entropy_gradient x)))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (mult eta (entropy_gradient x)))).
  apply (plus_zero (mult eta (entropy_gradient x))).
Qed.

(* K0' 反向差：x − x' == −(η·g(x)) *)
Lemma eg_step_neg_diff : forall x : R,
  Id (minus x (dynamics x)) (opp (mult eta (entropy_gradient x))).
Proof.
  intros x. unfold minus.
  apply (id_trans (id_cong (fun z => plus x z)
                           (id_cong opp (dynamics_gradient_step x)))).
  apply (id_trans (id_cong (fun z => plus x z)
                           (opp_plus x (mult eta (entropy_gradient x))))).
  apply (id_trans (plus_assoc x (opp x) (opp (mult eta (entropy_gradient x))))).
  apply (id_trans (id_cong (fun z => plus z (opp (mult eta (entropy_gradient x))))
                           (plus_opp x))).
  apply (id_trans (plus_comm zero (opp (mult eta (entropy_gradient x))))).
  apply (plus_zero (opp (mult eta (entropy_gradient x)))).
Qed.

(* 辅助：严格减正 a < b ⟹ 0 < b − a（根 ConvergenceCauchy 区 minus_pos 同构） *)
Lemma eg_minus_pos : forall u v : R, lt u v -> lt zero (minus v u).
Proof.
  intros u v Huv. unfold minus.
  apply (lt_id_l zero (plus u (opp u)) (plus v (opp u)) (id_sym (plus_opp u))).
  apply (lt_plus_compat_lt_le u v (opp u) (opp u) Huv (le_refl (opp u))).
Qed.

(* ===== 件 1 核 A：切线在 x' 处反向使用 ⟹ 增量 ≥ η·g(x)·g(x') =====
   切线（上界控制）在 x' 处取 y := x：
     e ≤ e' + g'·(x − x') = e' − g'·(η·g) ⟹ e' − e ≥ g'·(η·g) *)
Lemma eg_tangent_shift : forall x : R,
  le (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x.
  pose proof (entropy_tangent (dynamics x) x) as Ht.
  (* Ht 换形：minus x x' == −(η·g)；g'·(−η·g) == −(g'·(η·g)) *)
  assert (Ht1 : le (entropy x)
                   (plus (entropy (dynamics x))
                         (opp (mult (entropy_gradient (dynamics x))
                                    (mult eta (entropy_gradient x)))))).
  { apply (le_id_r _ (plus (entropy (dynamics x))
                           (mult (entropy_gradient (dynamics x))
                                 (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => plus (entropy (dynamics x)) z)
                     (id_trans (id_cong (fun z => mult (entropy_gradient (dynamics x)) z)
                                        (eg_step_neg_diff x))
                               (opp_mult_l (entropy_gradient (dynamics x))
                                           (mult eta (entropy_gradient x))))).
    - exact Ht. }
  (* 两边加 W := g'·(η·g) 移项：le e (e' − W) ⟹ le (e + W) e'
     链：le_plus_compat Ht1 (le_refl W) 得 le (e + W) ((e' − W) + W)，
     右端 == e'（assoc + plus_opp + plus_zero），le_id_r 直接收口 *)
  assert (Ht2 : le (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
  { pose proof (le_plus_compat (entropy x)
                               (plus (entropy (dynamics x))
                                     (opp (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               (mult (entropy_gradient (dynamics x))
                                     (mult eta (entropy_gradient x)))
                               Ht1 (le_refl (mult (entropy_gradient (dynamics x))
                                                  (mult eta (entropy_gradient x))))) as Hadd.
    apply (le_id_r (plus (entropy x)
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (plus (plus (entropy (dynamics x))
                               (opp (mult (entropy_gradient (dynamics x))
                                          (mult eta (entropy_gradient x)))))
                         (mult (entropy_gradient (dynamics x))
                               (mult eta (entropy_gradient x))))
                   (entropy (dynamics x))).
    - exact (id_trans (id_sym (plus_assoc (entropy (dynamics x))
                                          (opp (mult (entropy_gradient (dynamics x))
                                                     (mult eta (entropy_gradient x))))
                                          (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))))
                      (id_trans (id_cong (fun z => plus (entropy (dynamics x)) z)
                                         (id_trans (plus_comm (opp (mult (entropy_gradient (dynamics x))
                                                                            (mult eta (entropy_gradient x))))
                                                              (mult (entropy_gradient (dynamics x))
                                                                    (mult eta (entropy_gradient x))))
                                                   (plus_opp (mult (entropy_gradient (dynamics x))
                                                                   (mult eta (entropy_gradient x))))))
                                (plus_zero (entropy (dynamics x))))).
    - exact Hadd. }
  (* 两边加 opp e 提取：le (e + W) e' ⟹ le W (e' − e) == minus e' e *)
  apply (le_id_l (mult (entropy_gradient (dynamics x)) (mult eta (entropy_gradient x)))
                 (plus (plus (entropy x)
                             (mult (entropy_gradient (dynamics x))
                                   (mult eta (entropy_gradient x))))
                       (opp (entropy x)))).
  - exact (id_trans (id_trans (id_sym (plus_zero (mult (entropy_gradient (dynamics x))
                                                      (mult eta (entropy_gradient x)))))
                              (id_cong (fun z => plus (mult (entropy_gradient (dynamics x))
                                                             (mult eta (entropy_gradient x))) z)
                                       (id_sym (plus_opp (entropy x)))))
                    (id_trans (plus_assoc (mult (entropy_gradient (dynamics x))
                                                (mult eta (entropy_gradient x)))
                                          (entropy x) (opp (entropy x)))
                              (id_cong (fun z => plus z (opp (entropy x)))
                                       (plus_comm (mult (entropy_gradient (dynamics x))
                                                        (mult eta (entropy_gradient x)))
                                                  (entropy x))))).
  - exact (le_plus_compat (plus (entropy x)
                                (mult (entropy_gradient (dynamics x))
                                      (mult eta (entropy_gradient x))))
                          (entropy (dynamics x))
                          (opp (entropy x)) (opp (entropy x))
                          Ht2 (le_refl (opp (entropy x)))).
Qed.

(* ===== 件 1 核 B：Lipschitz 单边提取 ⟹ g' ≥ (1 − L·η)·g ===== *)
Lemma eg_grad_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (minus one (mult L eta)) (entropy_gradient x))
     (entropy_gradient (dynamics x)).
Proof.
  intros x Hgx.
  (* (i) |x' − x| == η·g(x)（η>0、g>0：abs_pos + abs_mult + abs_opp） *)
  assert (Hstep : Id (minus (dynamics x) x) (mult eta (entropy_gradient x)))
    by exact (eg_step_diff x).
  assert (Hha : lt zero (mult eta (entropy_gradient x)))
    by exact (mult_positive eta (entropy_gradient x) eta_pos Hgx).
  assert (Habsstep : Id (abs (minus (dynamics x) x))
                        (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs Hstep)).
    apply (id_trans (abs_mult eta (entropy_gradient x))).
    exact (id_cong2 (fun u v => mult u v) (abs_pos eta eta_pos) (abs_pos _ Hgx)). }
  assert (Habsneg : Id (abs (minus x (dynamics x)))
                       (mult eta (entropy_gradient x))).
  { apply (id_trans (id_cong abs (eg_step_neg_diff x))).
    apply (id_trans (abs_opp (mult eta (entropy_gradient x)))).
    apply (id_trans (id_cong abs (id_sym Hstep))).
    exact Habsstep. }
  (* (ii) Lipschitz 在 (x, x') 处：|g − g'| ≤ L·η·g *)
  assert (Hlip : le (abs (minus (entropy_gradient x) (entropy_gradient (dynamics x))))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_id_r _ (mult L (abs (minus x (dynamics x)))) _).
    - exact (id_cong (fun z => mult L z) Habsneg).
    - exact (gradient_lipschitz x (dynamics x)). }
  (* (iii) 单边提取：g − g' ≤ |g − g'| ≤ L·η·g（abs_ge_value） *)
  assert (Hone : le (minus (entropy_gradient x) (entropy_gradient (dynamics x)))
                    (mult L (mult eta (entropy_gradient x)))).
  { apply (le_trans _ (abs (minus (entropy_gradient x)
                                  (entropy_gradient (dynamics x)))) _).
    - exact (abs_ge_value (minus (entropy_gradient x)
                                 (entropy_gradient (dynamics x)))).
    - exact Hlip. }
  (* (iv) 移项：g − (Lη)g ≤ g'，即 (1 − Lη)·g ≤ g'
        链：加 g' 得 le g ((Lη)g + g')；加 opp((Lη)g) 得 le (g − (Lη)g) g' *)
  assert (H1 : le (entropy_gradient x)
                  (plus (mult L (mult eta (entropy_gradient x)))
                        (entropy_gradient (dynamics x)))).
  { apply (le_id_l (entropy_gradient x)
                   (plus (minus (entropy_gradient x)
                                (entropy_gradient (dynamics x)))
                         (entropy_gradient (dynamics x)))).
    - exact (id_sym (eg_minus_plus_cancel (entropy_gradient x)
                                          (entropy_gradient (dynamics x)))).
    - exact (le_plus_compat (minus (entropy_gradient x)
                                   (entropy_gradient (dynamics x)))
                            (mult L (mult eta (entropy_gradient x)))
                            (entropy_gradient (dynamics x)) (entropy_gradient (dynamics x))
                            Hone (le_refl (entropy_gradient (dynamics x)))). }
  assert (H2 : le (plus (entropy_gradient x)
                        (opp (mult L (mult eta (entropy_gradient x)))))
                  (entropy_gradient (dynamics x))).
  { apply (le_id_r _ (plus (plus (mult L (mult eta (entropy_gradient x)))
                                 (entropy_gradient (dynamics x)))
                           (opp (mult L (mult eta (entropy_gradient x)))))
                     (entropy_gradient (dynamics x))).
    - exact (id_trans (id_cong (fun z => plus z (opp (mult L (mult eta (entropy_gradient x)))))
                               (plus_comm (mult L (mult eta (entropy_gradient x)))
                                          (entropy_gradient (dynamics x))))
                      (id_trans (id_sym (plus_assoc (entropy_gradient (dynamics x))
                                                    (mult L (mult eta (entropy_gradient x)))
                                                    (opp (mult L (mult eta (entropy_gradient x))))))
                                (id_trans (id_cong (fun z => plus (entropy_gradient (dynamics x)) z)
                                                   (plus_opp (mult L (mult eta (entropy_gradient x)))))
                                          (plus_zero (entropy_gradient (dynamics x)))))).
    - exact (le_plus_compat (entropy_gradient x)
                            (plus (mult L (mult eta (entropy_gradient x)))
                                  (entropy_gradient (dynamics x)))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            (opp (mult L (mult eta (entropy_gradient x))))
                            H1 (le_refl (opp (mult L (mult eta (entropy_gradient x)))))). }
  (* (v) 换形：g + opp((Lη)g) == (1 − Lη)·g
        链：opp((Lη)g) == opp((L·η)g) == (opp(Lη))·g；再
        g + (opp(Lη))·g == 1·g + (opp(Lη))·g == (1 + opp(Lη))·g *)
  apply (le_id_l (mult (minus one (mult L eta)) (entropy_gradient x))
                 (plus (entropy_gradient x)
                       (opp (mult L (mult eta (entropy_gradient x)))))).
  - exact (id_sym
             (id_trans (id_cong (fun z => plus (entropy_gradient x) z)
                                (id_trans (id_cong opp (mult_assoc L eta (entropy_gradient x)))
                                          (id_sym (opp_mult_r (mult L eta) (entropy_gradient x)))))
                       (id_trans (id_cong (fun z => plus z (mult (opp (mult L eta))
                                                                 (entropy_gradient x)))
                                          (id_trans (id_sym (mult_one (entropy_gradient x)))
                                                    (mult_comm (entropy_gradient x) one)))
                                 (id_sym (mult_plus_distr_r one (opp (mult L eta))
                                                            (entropy_gradient x)))))).
  - exact H2.
Qed.

(* ============================================================
   件 1（交付）：entropy_step_gain_lower —— 一步熵增定量下界
     g(x) > 0 ⟹
     η(1 − L·η)·g(x)² ≤ entropy(dynamics x) − entropy(x)
   组装：核 B 乘 g > 0 再乘 η > 0，与核 A 级联。
   ============================================================ *)
Theorem entropy_step_gain_lower : forall x : R,
  lt zero (entropy_gradient x) ->
  le (mult (mult eta (minus one (mult L eta)))
           (mult (entropy_gradient x) (entropy_gradient x)))
     (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx.
  pose proof (eg_grad_lower x Hgx) as Hlow.
  (* 乘 g > 0（le_mult_compat）：(c₁·g)·g ≤ g'·g，左换形 assoc *)
  pose proof (le_mult_compat (mult (minus one (mult L eta)) (entropy_gradient x))
                             (entropy_gradient (dynamics x))
                             (entropy_gradient x) Hgx Hlow) as Hm1.
  assert (Hm1' : le (mult (minus one (mult L eta))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x)) (entropy_gradient x))).
  { apply (le_id_l _ (mult (mult (minus one (mult L eta)) (entropy_gradient x))
                           (entropy_gradient x)) _).
    - exact (mult_assoc (minus one (mult L eta)) (entropy_gradient x)
                        (entropy_gradient x)).
    - exact Hm1. }
  (* 乘 η > 0（le_mult_compat_r，左乘）：η·((1−Lη)·g²) ≤ η·(g'·g) *)
  pose proof (lt_le_iff zero eta (inl eta_pos)) as Hle_eta.
  pose proof (le_mult_compat_r eta
                             (mult (minus one (mult L eta))
                                   (mult (entropy_gradient x) (entropy_gradient x)))
                             (mult (entropy_gradient (dynamics x)) (entropy_gradient x))
                             Hle_eta Hm1') as Hm2.
  assert (Hm2' : le (mult (mult eta (minus one (mult L eta)))
                          (mult (entropy_gradient x) (entropy_gradient x)))
                    (mult (entropy_gradient (dynamics x))
                          (mult eta (entropy_gradient x)))).
  { apply (le_id_l _ (mult eta (mult (minus one (mult L eta))
                                     (mult (entropy_gradient x) (entropy_gradient x)))) _).
    - exact (id_sym (mult_assoc eta (minus one (mult L eta))
                                (mult (entropy_gradient x) (entropy_gradient x)))).
    - apply (le_id_r _ (mult eta (mult (entropy_gradient (dynamics x))
                                       (entropy_gradient x))) _).
      + exact (id_trans (mult_assoc eta (entropy_gradient (dynamics x)) (entropy_gradient x))
                        (id_trans (id_cong (fun z => mult z (entropy_gradient x))
                                           (mult_comm eta (entropy_gradient (dynamics x))))
                                  (id_sym (mult_assoc (entropy_gradient (dynamics x))
                                                      eta (entropy_gradient x))))).
      + exact Hm2. }
  exact (le_trans _ _ _ Hm2' (eg_tangent_shift x)).
Qed.

(* ============================================================
   件 2（交付）：entropy_gain_positive —— 增量正性充分条件版
     0 < η、0 < L、ηL < 1、g(x) > 0 ⟹ 0 < entropy(x') − entropy(x)
   （正性条件取 ηL < 1 而非草案 ημ < 1：μ 只控制上界不控制过冲，
     见文件头推导注记；负支 g < 0 需符号三分判定，构造性降级单侧版。）
   ============================================================ *)
Theorem entropy_gain_positive : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt zero (minus (entropy (dynamics x)) (entropy x)).
Proof.
  intros x Hgx HetaL.
  assert (Hc : lt zero (minus one (mult L eta)))
    by exact (eg_minus_pos (mult L eta) one HetaL).
  assert (Hc1 : lt zero (mult eta (minus one (mult L eta))))
    by exact (mult_positive eta (minus one (mult L eta)) eta_pos Hc).
  assert (Haa : lt zero (mult (entropy_gradient x) (entropy_gradient x)))
    by exact (mult_positive (entropy_gradient x) (entropy_gradient x) Hgx Hgx).
  assert (HA : lt zero (mult (mult eta (minus one (mult L eta)))
                             (mult (entropy_gradient x) (entropy_gradient x))))
    by exact (mult_positive (mult eta (minus one (mult L eta)))
                            (mult (entropy_gradient x) (entropy_gradient x))
                            Hc1 Haa).
  pose proof (entropy_step_gain_lower x Hgx) as Hlow.
  exact (lt_le_trans zero _ _ HA Hlow).
Qed.

(* ============================================================
   件 3（对照注记 + 交付推论）：second_law_quant
   根 L27778–27803 SecondLaw 区：strict_entropy_increase 是接口假设
   （Variable），second_law_irreversible = `apply strict_entropy_increase`
   （T2 假设搬运，探针实证导出形态两处同现同一前提）。本件以具体熵梯度
   动力学 + 诚实充分条件（ηL < 1、g(x) > 0）产出同一结论
   lt (entropy x) (entropy (dynamics x))——旧件可作退役注记：
   其接口前提在本件条件下由 entropy_gain_positive 构造性供给。
   ============================================================ *)
Theorem second_law_quant : forall x : R,
  lt zero (entropy_gradient x) ->
  lt (mult L eta) one ->
  lt (entropy x) (entropy (dynamics x)).
Proof.
  intros x Hgx HetaL.
  pose proof (entropy_gain_positive x Hgx HetaL) as Hpos.
  apply (lt_id_r (entropy x)
                 (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))
                 (entropy (dynamics x))).
  - exact (eg_minus_plus_cancel (entropy (dynamics x)) (entropy x)).
  - apply (lt_id_l (entropy x) (plus zero (entropy x))
                   (plus (minus (entropy (dynamics x)) (entropy x)) (entropy x))).
    + exact (id_trans (id_sym (plus_zero (entropy x)))
                      (plus_comm (entropy x) zero)).
    + exact (lt_plus_compat_lt_le zero (minus (entropy (dynamics x)) (entropy x))
                                  (entropy x) (entropy x)
                                  Hpos (le_refl (entropy x))).
Qed.

End EntropyGainQuant.

(* ---------- UpSigMigrate ---------- *)
Module SigMigrate.
(* UpSigMigrate.v — 抽象层签名对接试点：Id 系 → setoid 系（req := real_eq）
   试点 1（必做）: req_free_energy_kl_decomp —— F[p] == F[p_b] + D·KL(p‖p_b) 的
     setoid 签名版：Section Context 换 RealInterfaceEnhancedSetoid；
     Id → req 全迁移；normalized := req (Σ p) one；log 族带正性前提。
   试点 2（尽力）: req_attention_is_gibbs_temp —— 三前提 + 逐点结论全 req。
   纪律：纯构造性；Set 层（req/lt/le 均 Set 值，语句零 Prop）；
   中间等式全走 req 字段（req_trans 链 + compat 桥），destruct 消去不可用。 *)
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 试点 1：FreeEnergyMinimization 节的 setoid 签名对接           *)
(*   Id 原件：CW L15759-16440（Context {RI : RealInterfaceEnhanced}， *)
(*   StateSpace/SumOver 为 Id 系类，其字段带 Id——故本试点以       *)
(*   req 签名的求和三性质作为节 Hypothesis（= SumOver 类的       *)
(*   setoid 对接面），对接成本计入报告；上游两条 Id 系已证        *)
(*   引理（energy_in_log_boltzmann / free_energy_boltzmann）以    *)
(*   req 签名桥 Hypothesis 承接，全量迁移外推见报告。            *)
(* ============================================================ *)
Section ReqFreeEnergyPilot.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* ---- SumOver 的 req 签名对接面（Id 系 SumOver L1400 的 setoid 镜像） ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* ---- 节参数（对齐 Id 系 L15778-15791） ---- *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- 节内定义（setoid 惯例形态） ---- *)
Definition cwe_positive_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition cwe_boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
(* log 族带正性前提（setoid 接口 L40570），故 free_energy 限定在正性分布上 *)
Definition cwe_free_energy (p : S -> R) (Hp : cwe_positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition cwe_normalized (p : S -> R) : Set := req (sumf p) one.
Definition rminus (a b : R) : R := plus a (opp b).

(* ---- Boltzmann 分布正性（setoid log 前提所需；接口字段直接组装） ---- *)
Lemma req_boltzmann_positive : cwe_positive_dist cwe_boltzmann_dist.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* ---- 上游 Id 系已证成果的 req 签名桥（Id 原件 L16116 / L15945） ---- *)
Hypothesis energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))
                           (log Z Z_pos)))).
Hypothesis free_energy_boltzmann_bridge :
  req (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).

(* ============================================================ *)
(* A. 代数前奏：req 版 opp 代数（接口字段纯推导，零 destruct，   *)
(*    全 req_trans 链 + compat 桥——Id 系 rewrite 消去不可用）    *)
(* ============================================================ *)

(* 加零右形式：plus_zero 字段只有左形式，右形式走 comm 桥 *)
Lemma req_plus_zero_r : forall a : R, req (plus zero a) a.
Proof.
  intro a.
  exact (req_trans (plus zero a) (plus a zero) a (plus_comm zero a) (plus_zero a)).
Qed.

(* 单位元左形式：mult_one 字段只有右形式 *)
Lemma req_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

(* 左消去：opp 唯一性的引擎（Id 系经 destruct/注入免费获得，此处 7 段链） *)
Lemma req_add_cancel_l : forall (u v w : R),
  req (plus u v) (plus w v) -> req u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* 双重负号：opp (opp a) == a（两次 plus_opp + 消去；Id 系 double_neg 引理） *)
Lemma req_double_neg : forall a : R, req (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

(* 负号分配：opp (a+b) == opp a + opp b（Id 系 opp_plus 引理） *)
Lemma req_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b)) (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b)) (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a) (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a) (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

(* mult a (opp b) == opp (mult a b)（Id 系 opp_mult_l 引理） *)
Lemma req_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b)) (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b)) (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* mult (opp a) b == opp (mult a b)（Id 系 opp_mult_r 引理，经 comm 桥） *)
Lemma req_opp_mult_l : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_mult_opp_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
  Qed.

(* ============================================================ *)
(* B. 求和层 req 引理（SumOver req 对接面之上的移植）            *)
(* ============================================================ *)

(* Σ opp f == opp Σ f（Id 原件 L15801 sum_opp） *)
Lemma req_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      apply (req_sym (mult one (f s)) (f s)). apply req_mult_one_l.
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_l.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_l.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)). apply req_mult_one_l.
Qed.

(* Boltzmann 分布归一化（Id 原件 L15846 boltzmann_normalized 的 req 版） *)
Lemma req_boltzmann_normalized : req (sumf cwe_boltzmann_dist) one.
Proof.
  apply (req_trans (sumf cwe_boltzmann_dist)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
                      (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z)
                     one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * apply (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
        exact partition_condition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* ============================================================ *)
(* C. 逐点分解（Id 原件 L16198 p_times_energy_decomp 的 req 版） *)
(* ============================================================ *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s)) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  assert (HlegA : req (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
  { apply (req_trans (mult (p s) (base_loss s)) (mult (p s) (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
    - apply (req_mult_compat (p s) (p s) (base_loss s) (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
      * apply req_refl.
      * apply (energy_in_log_boltzmann_bridge s).
    - apply (req_mult_opp_l (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). }
  assert (Hswap : req (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
  { apply (req_trans (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult (p s) D) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
    - apply mult_assoc.
      - apply (req_trans (mult (mult (p s) D) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
        * apply (req_mult_compat (mult (p s) D) (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))).
          { apply mult_comm. }
          { apply req_refl. }
        * apply (req_sym (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). apply mult_assoc.
  }
  assert (Hdist2 : req (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
  { apply (req_trans (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (plus (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    - apply (req_mult_compat D D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (plus (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))).
      + apply req_refl.
      + apply distrib.
    - apply distrib. }
  apply (req_trans (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
  - exact HlegA.
  - apply (req_trans (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    + apply (req_opp_compat (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))). exact Hswap.
    + apply (req_trans (opp (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
      * apply (req_opp_compat (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))). exact Hdist2.
      * apply req_opp_plus.
Qed.
(* ============================================================ *)
(* D. 旗舰迁移：req_free_energy_kl_decomp                        *)
(*    F[p] == F[p_b] + D·KL(p‖p_b)（Id 原件 L16259 的 setoid 签名版） *)
(*    记号：lgpb s := log (cwe_boltzmann_dist s) Hpb；lgps s := log (p s) Hp； *)
(*    A := D·Σ p·lgpb；B := D·Σ p·lgps；DlgZ := D·log Z；        *)
(*    KL := fun s => p s · (lgps s − lgpb s)；Fpb := cwe_free_energy p_b *)
(* ============================================================ *)
Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : cwe_normalized p) (p0 : cwe_positive_dist p),
    req (cwe_free_energy p p0)
        (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
              (mult D (sumf (fun s =>
                mult (p s) (rminus (log (p s) (p0 s))
                                   (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
Proof.
  intros p Hp p0.
  (* 桥：F[p_b] == mult (opp D) lgZ == opp (D·lgZ)（Id 系步骤 2 的 req 形态） *)
  assert (Hfb' : req (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
                     (opp (mult D (log Z Z_pos)))).
  { apply (req_trans (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
                     (mult (opp D) (log Z Z_pos))
                     (opp (mult D (log Z Z_pos)))).
    - exact free_energy_boltzmann_bridge.
    - apply req_opp_mult_l. }
  (* 步骤 1：Σ p·E == opp A + opp DlgZ（Id 原件 Hse） *)
  assert (Hse : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                          (opp (mult D (log Z Z_pos))))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (sumf (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                          (opp (mult D (mult (p s) (log Z Z_pos))))))
                     (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    - apply (sum_ext (fun s => mult (p s) (base_loss s))
                     (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                    (opp (mult D (mult (p s) (log Z Z_pos)))))).
      { intro s. apply req_p_times_energy_decomp. }
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))).
      { apply sum_add. }
      { apply (req_plus_compat (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                               (opp (mult D (log Z Z_pos)))).
        - (* Σ opp(D·p·lgpb) == opp(D·Σ p·lgpb)：sum_opp + D 线性提取 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
          { apply req_sum_opp. }
          { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                  (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
            { apply (sum_linear D (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))). } }
        - (* Σ opp(D·p·lgZ) == opp(D·lgZ)：sum_opp + D 线性 + Σ p·lgZ = lgZ·Σp = lgZ 归一化链 *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          { apply req_sum_opp. }
          { apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                             (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                             (opp (mult D (log Z Z_pos)))).
            { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                    (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))).
              { apply (sum_linear D (fun s => mult (p s) (log Z Z_pos))). } }
            { apply (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                    (mult D (log Z Z_pos))).
              { apply (req_mult_compat D D (sumf (fun s => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
                { apply req_refl. }
                { apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                   (sumf (fun s => mult (log Z Z_pos) (p s)))
                                   (log Z Z_pos)).
                  { apply (sum_ext (fun s => mult (p s) (log Z Z_pos)) (fun s => mult (log Z Z_pos) (p s))).
                    { intro s2. apply mult_comm. } }
                  { apply (req_trans (sumf (fun s => mult (log Z Z_pos) (p s)))
                                     (mult (log Z Z_pos) (sumf p))
                                     (log Z Z_pos)).
                    { apply (sum_linear (log Z Z_pos) p). }
                    { apply (req_trans (mult (log Z Z_pos) (sumf p))
                                       (mult (log Z Z_pos) one)
                                       (log Z Z_pos)).
                      { apply (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one).
                        { apply req_refl. }
                        { exact Hp. } }
                      { apply mult_one. } } } } } } }
  }
  }
  (* 步骤 3：D·KL == B + opp A（Id 原件 Hkl） *)
  assert (Hkl : req (mult D (sumf (fun s =>
                      mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                    (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                          (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { assert (Hpt2 : forall s : S,
        req (mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
            (plus (mult (p s) (log (p s) (p0 s)))
                  (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
    { intro s. unfold rminus.
      apply (req_trans (mult (p s) (plus (log (p s) (p0 s)) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s))) (mult (p s) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s)))
                             (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
      { apply distrib. }
      { apply (req_plus_compat (mult (p s) (log (p s) (p0 s))) (mult (p s) (log (p s) (p0 s)))
                               (mult (p s) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
                               (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))).
        { apply req_refl. }
        { apply req_mult_opp_l. } } }
    assert (Hinner : req (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply (req_trans (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                       (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                             (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (sum_ext (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
                       (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
        { exact Hpt2. } }
      { apply (req_trans (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
        { apply sum_add. }
        { apply (req_plus_compat (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                 (sumf (fun s => opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                 (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
          { apply req_refl. }
          { apply req_sum_opp. } } } }
    apply (req_trans (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                     (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply (req_mult_compat D D
                             (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                             (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply req_refl. }
      { exact Hinner. } }
    apply (req_trans (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply distrib. }
    apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply req_refl. }
    { apply req_mult_opp_l. } }

  (* 步骤 4：环代数坍缩（Id 原件 Hfin：(opp A + opp DlgZ) + B → opp DlgZ + (B + opp A)） *)
  assert (Hfin : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                     (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))))).
  { set (A := (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
    set (DlgZ := (mult D (log Z Z_pos))).
    set (B := (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    apply (req_trans (plus (plus (opp A) (opp DlgZ)) B)
                     (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_sym (plus (opp A) (plus (opp DlgZ) B))
                     (plus (plus (opp A) (opp DlgZ)) B)).
      apply plus_assoc. }
    apply (req_trans (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp A) (plus B (opp DlgZ)))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (opp A) (opp A) (plus (opp DlgZ) B) (plus B (opp DlgZ))).
      { apply req_refl. }
      { apply plus_comm. } }
    apply (req_trans (plus (opp A) (plus B (opp DlgZ)))
                     (plus (plus (opp A) B) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply plus_assoc. }
    apply (req_trans (plus (plus (opp A) B) (opp DlgZ))
                     (plus (plus B (opp A)) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (plus (opp A) B) (plus B (opp A)) (opp DlgZ) (opp DlgZ)).
      { apply plus_comm. }
      { apply req_refl. } }
    apply plus_comm. }
  (* 总装：Hleg1（cwe_free_energy p 定义展开 conversion + Hse 于 compat 槽）；Hleg2（Hfin + Hfb'/Hkl 反向收尾槽） *)
  assert (Hleg1 : req (cwe_free_energy p p0) (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))).
  { unfold cwe_free_energy.
    apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s))) (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    { exact Hse. }
    { apply req_refl. } }
  assert (Hleg2 : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))) (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { apply (req_trans (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                      (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))))
                      (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { exact Hfin. }
    { apply (req_plus_compat (opp (mult D (log Z Z_pos))) (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (req_sym (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (opp (mult D (log Z Z_pos)))). exact Hfb'. }
      { apply (req_sym (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))). exact Hkl. } } }
  exact (req_trans _ _ _ Hleg1 Hleg2).
Qed.

End ReqFreeEnergyPilot.

(* ============================================================ *)
(* 试点 2（尽力）：req_attention_is_gibbs_temp                    *)
(*   Id 原件：CW L28634（AttentionGibbsBridge 节，L27929-28710）。*)
(*   三前提 + 逐点结论全 req 迁移；节内基础设施（exp_pos_fn /      *)
(*   partition_function_temp / softmax_temp / boltzmann_factor /  *)
(*   Z_thermo / boltzmann_dist_attn）按同形定义重建。             *)
(*   接口缺口发现：RealInterfaceEnhancedSetoid 无 exp_neg 兼容     *)
(*   字段（Id 系 id_cong 免费可得），以 req 签名桥 Hypothesis      *)
(*   承接——Real 实例由 cauchy_real_exp_wd 满足（L40440 先例）。    *)
(* ============================================================ *)
Section ReqGibbsPilot.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_pos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
(* 接口缺口桥：exp_neg 的 req 兼容（字段缺失，见上注） *)
Hypothesis req_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).

Variable T : R.
Variable T_pos : lt zero T.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.

Definition cwe_exp_pos_fn (x : R) : R := exp_neg (opp x).
Definition cwe_partition_function_temp : R :=
  sumf (fun s => cwe_exp_pos_fn (mult (inv_pos T T_pos) (z s))).
Hypothesis partition_function_temp_pos : lt zero cwe_partition_function_temp.
Definition cwe_softmax_temp (s : S) : R :=
  mult (cwe_exp_pos_fn (mult (inv_pos T T_pos) (z s)))
       (inv_pos cwe_partition_function_temp partition_function_temp_pos).
Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).
Definition Z_thermo : R := sumf boltzmann_factor.
Variable Z_thermo_pos : lt zero Z_thermo.
Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

Theorem req_attention_is_gibbs_temp :
  (req (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  (req Z_thermo cwe_partition_function_temp) ->
  forall s : S, req (cwe_softmax_temp s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  assert (Hf : req (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                   (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  { apply (req_exp_neg_ext (opp (mult (inv_pos T T_pos) (z s)))
                           (mult (inv_pos D D_pos) (energy s))).
    apply (req_trans (opp (mult (inv_pos T T_pos) (z s)))
                     (mult (inv_pos T T_pos) (opp (z s)))
                     (mult (inv_pos D D_pos) (energy s))).
    - exact (req_sym (mult (inv_pos T T_pos) (opp (z s)))
                     (opp (mult (inv_pos T T_pos) (z s)))
                     (req_mult_opp_l (inv_pos T T_pos) (z s))).
    - apply (req_mult_compat (inv_pos T T_pos) (inv_pos D D_pos) (opp (z s)) (energy s)).
      + exact HD.
      + apply (req_sym (energy s) (opp (z s))). apply Henergy. }
  assert (Hie : req (inv_pos Z_thermo Z_thermo_pos)
                    (inv_pos cwe_partition_function_temp partition_function_temp_pos)).
  { apply (inv_pos_ext Z_thermo cwe_partition_function_temp
                       Z_thermo_pos partition_function_temp_pos HZ). }
  unfold cwe_softmax_temp, boltzmann_dist_attn, boltzmann_factor, cwe_exp_pos_fn.
  apply (req_trans (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (inv_pos cwe_partition_function_temp partition_function_temp_pos))
                       (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos Z_thermo Z_thermo_pos))
                       (mult (inv_pos Z_thermo Z_thermo_pos)
                             (exp_neg (mult (inv_pos D D_pos) (energy s))))).
    { apply (req_mult_compat (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos cwe_partition_function_temp partition_function_temp_pos)
                             (inv_pos Z_thermo Z_thermo_pos)).
      { exact Hf. }
      { apply (req_sym (inv_pos Z_thermo Z_thermo_pos) (inv_pos cwe_partition_function_temp partition_function_temp_pos)). exact Hie. } }
    apply mult_comm.
Qed.

End ReqGibbsPilot.
End SigMigrate.

(* ---------- UpMinP ---------- *)
From Stdlib Require Import List Arith Lia.
(* ============================================================ *)
(* UpMinP.v —— Min-P 截断质量的熵刻画（Real 层 list 离散世界）    *)
(*                                                              *)
(* 主定理（统一根内两条已知界的熵版）：                          *)
(*   件 1  entropy_ge_neg_log_p_max :                            *)
(*         S ≥ −log(p_max)（熵 ≥ 最大概率的负对数）              *)
(*   件 2  dropped_le_one_minus_exp_neg_S :                      *)
(*         dropped ≤ 1 − e^−S（Min-P 截断质量的熵上界）          *)
(*   件 3  dropped_le_one_minus_inv_n :                          *)
(*         dropped ≤ 1 − 1/N（均匀特例，与根 L31849 对齐）       *)
(*                                                              *)
(* 证明链：dropped == 1 − kept（定义性）；kept ≥ p_max（pick_max *)
(* 必被保留，见 um_kept_ge_pmax）；p_max ≥ e^−S：逐项 k ≤ p_max   *)
(* ⟹ −log k ≥ −log p_max ⟹ S = Σ k·(−log k) ≥ −log p_max（权重  *)
(* 非负加权 + 归一化 Σk = 1）⟹ e^−S ≤ p_max（exp antitone +      *)
(* cw_log_exp_right）⟹ dropped ≤ 1 − e^−S。                     *)
(*                                                              *)
(* 简化世界：tokens : list Real（概率表，逐项正、和 = 1）；      *)
(* p_max := fold real_max（逐点上界 um_fmax_ge_nth + 可达性       *)
(* um_fmax_mem_nth 双引理）；熵/保留质量均以 seq 0 N 下标表求和， *)
(* 下标界全用扫描库 Set 层编码 NatLt := Id (ltb) true——          *)
(* 索引和引理（um_rls_le_N / um_rls_nonneg_N /                   *)
(* um_rls_single_le_N）逐点假设为 NatLt 前提函数，无 Prop 解构、 *)
(* 无递归 Set 谓词匹配，提取零 Obj.magic；Min-P 保留判定以三分    *)
(* 判定元 um_trich_probe（a ≤ b ∨ b < a，镜像根内 ord_le_dec     *)
(* 结构域字段）携带——纯构造性，无经典公理。                      *)
(* 纪律：零公理、零搁置、零参数化声明、零经典逻辑（纯构造性）；*)
(*       语句全 Set 层（real_lt/real_le/real_eq + Or/sigT/prod + *)
(*       NatLt），无 Prop 前提；全部 Qed. 闭合；                 *)
(*       Real 层顶层名（um_ 前缀防遮蔽）。                       *)
(* 注意：CW214KL_scan 将 S 遮蔽为 Set，nat 模式一律               *)
(* Datatypes.O / Datatypes.S。提取探针见 probe_minp_extract.v。  *)
(* ============================================================ *)


(* ============================================================ *)
(* 0. 通用桥（Real 层，Section 外，全局可复用）                  *)
(* ============================================================ *)

(* lt ⟹ le（real_le 的 Or 编码左支） *)
Lemma um_lt_le : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H. exact (inl H).
Qed.

(* eq ⟹ le（Or 编码右支） *)
Lemma um_eq_le : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  exact RealSetoid.real_eq_le.
Qed.

(* 0 ≤ y ⟹ x ≤ x + y（加非负数） *)
Lemma um_le_add_l : forall x y : Real,
  real_le real_zero y -> real_le x (real_plus x y).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_id_l x (real_plus x real_zero) (real_plus x y)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat.
    + apply real_le_refl.
    + exact Hy.
Qed.

(* 0 ≤ a、0 ≤ b ⟹ 0 ≤ a + b *)
Lemma um_add_nonneg : forall a b : Real,
  real_le real_zero a -> real_le real_zero b ->
  real_le real_zero (real_plus a b).
Proof.
  intros a b Ha Hb.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat.
    + exact Ha.
    + exact Hb.
Qed.

(* 0 ≤ y ⟹ x ≤ y + x（加非负数于左） *)
Lemma um_le_add_r : forall x y : Real,
  real_le real_zero y -> real_le x (real_plus y x).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_id_l x (real_plus real_zero x) (real_plus y x)).
  - apply (real_eq_trans x (real_plus x real_zero)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_plus_comm.
  - apply real_le_plus_compat.
    + exact Hy.
    + apply real_le_refl.
Qed.

(* 1·x == x（左单位；real_mult_one 是右单位版） *)
Lemma um_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* Empty_set → False 桥：扫描库把 Not 定义为 Set 层（A → Empty_set），
   归谬项须跨入 Prop 的 False（仅证明内部使用，语句层无 Prop） *)
Lemma um_Emptyset_false : Empty_set -> False.
Proof.
  intro e. exact (match e with end).
Qed.

(* ============================================================ *)
(* 1. 索引表求和（seq 形态）：nreal / 位移 / nth 桥 / 常值        *)
(* ============================================================ *)

(* nreal：nat → Real 嵌入（表长 N 的 Real 化） *)
Fixpoint um_nreal (n : nat) : Real :=
  match n with
  | Datatypes.O => real_zero
  | Datatypes.S k => real_plus real_one (um_nreal k)
  end.

Lemma um_nreal_pos : forall n : nat,
  real_lt real_zero (um_nreal (Datatypes.S n)).
Proof.
  induction n as [| k IH].
  - apply (real_lt_eq_lt real_zero real_one
                         (real_plus real_one (um_nreal Datatypes.O))).
    + apply real_lt_zero_one.
    + apply real_eq_sym. apply real_plus_zero.
  - apply real_plus_positive.
    + apply real_lt_zero_one.
    + exact IH.
Qed.

(* 由下标界给 nreal 正性：NatLt i n ⟹ n = S m ⟹ nreal n > 0 *)
Lemma um_nreal_pos_of_lt : forall (n i : nat),
  NatLt i n -> real_lt real_zero (um_nreal n).
Proof.
  intros n i Hi. destruct n as [| m].
  - exfalso. exact (um_Emptyset_false (id_false_true Hi)).
  - exact (um_nreal_pos m).
Qed.

(* 求和位移：Σ_{seq (S s) n} f == Σ_{seq s n} (fun i => f (S i)) *)
Lemma um_seq_shift : forall (f : nat -> Real) (n s : nat),
  real_eq (real_list_sum nat f (seq (Datatypes.S s) n))
          (real_list_sum nat (fun i : nat => f (Datatypes.S i)) (seq s n)).
Proof.
  intros f n. induction n as [| n IH]; intro s.
  - cbn [seq real_list_sum]. apply real_eq_refl.
  - cbn [seq real_list_sum].
    apply (RealSetoid.real_eq_plus_compat (f (Datatypes.S s))
             (real_list_sum nat f (seq (Datatypes.S (Datatypes.S s)) n))
             (f (Datatypes.S s))
             (real_list_sum nat (fun i : nat => f (Datatypes.S i))
                                   (seq (Datatypes.S s) n))).
    + apply real_eq_refl.
    + exact (IH (Datatypes.S s)).
Qed.

(* skipn 求和步进：nth k rest 0 + Σ (skipn (S k) rest)
                    == Σ (skipn k rest) *)
Lemma um_skipn_sum_step : forall (k : nat) (rest : list Real),
  real_eq (real_plus (nth k rest real_zero)
                     (real_list_sum Real (fun x : Real => x)
                                   (skipn (Datatypes.S k) rest)))
          (real_list_sum Real (fun x : Real => x) (skipn k rest)).
Proof.
  induction k as [| k IH]; intro rest.
  - destruct rest as [| q rest2].
    + cbn [nth skipn real_list_sum]. apply real_plus_zero.
    + cbn [nth skipn real_list_sum].
      apply (RealSetoid.real_eq_plus_compat q
               (real_list_sum Real (fun x : Real => x) rest2)
               q (real_list_sum Real (fun x : Real => x) rest2)).
      * apply real_eq_refl.
      * apply real_eq_refl.
  - destruct rest as [| q rest2].
    + cbn [nth skipn real_list_sum]. apply real_plus_zero.
    + cbn [nth skipn real_list_sum].
      exact (IH rest2).
Qed.

(* nth 桥（主引理）：Σ_{seq s (length l)} nth i l 0 == Σ (skipn s l) *)
Local Open Scope nat_scope.

Lemma um_seq_nth_sum : forall (l : list Real) (s : nat),
  real_eq (real_list_sum nat (fun i : nat => nth i l real_zero)
                             (seq s (length l)))
          (real_list_sum Real (fun x : Real => x) (skipn s l)).
Proof.
  induction l as [| p rest IH]; intro s.
  - destruct s as [| k].
    + cbn [seq length skipn real_list_sum]. apply real_eq_refl.
    + cbn [seq length skipn real_list_sum]. apply real_eq_refl.
  - destruct s as [| k].
    + (* s = 0：p + Σ_{seq 1 n} nth i (p::rest) 0 == p + Σ rest *)
      cbn [seq length skipn real_list_sum].
      apply (RealSetoid.real_eq_plus_compat
                (nth Datatypes.O (p :: rest) real_zero)
                (real_list_sum nat
                   (fun i : nat => nth i (p :: rest) real_zero)
                   (seq 1 (length rest)))
                p
                (real_list_sum Real (fun x : Real => x) rest)).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_list_sum nat
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (seq 1 (length rest)))
                 (real_list_sum nat
                    (fun i : nat => nth i rest real_zero)
                    (seq 0 (length rest)))).
        -- exact (um_seq_shift
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (length rest) 0).
        -- exact (IH 0).
    + (* s = S k：位移 + IH(rest, S k) + 步进引理三段拼合 *)
      cbn [seq length real_list_sum].
      apply (real_eq_trans
               (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                          (real_list_sum nat
                             (fun i : nat => nth i (p :: rest) real_zero)
                             (seq (Datatypes.S (Datatypes.S k))
                                  (length rest))))
               (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                          (real_list_sum nat
                             (fun i : nat => nth i rest real_zero)
                             (seq (Datatypes.S k) (length rest))))).
      * apply (RealSetoid.real_eq_plus_compat
                  (nth (Datatypes.S k) (p :: rest) real_zero)
                  (real_list_sum nat
                     (fun i : nat => nth i (p :: rest) real_zero)
                     (seq (Datatypes.S (Datatypes.S k)) (length rest)))
                  (nth (Datatypes.S k) (p :: rest) real_zero)
                  (real_list_sum nat
                     (fun i : nat => nth i rest real_zero)
                     (seq (Datatypes.S k) (length rest)))).
        -- apply real_eq_refl.
        -- exact (um_seq_shift
                    (fun i : nat => nth i (p :: rest) real_zero)
                    (length rest) (Datatypes.S k)).
      * apply (real_eq_trans
                 (real_plus (nth (Datatypes.S k) (p :: rest) real_zero)
                            (real_list_sum nat
                               (fun i : nat => nth i rest real_zero)
                               (seq (Datatypes.S k) (length rest))))
                 (real_plus (nth k rest real_zero)
                            (real_list_sum Real (fun x : Real => x)
                                          (skipn (Datatypes.S k) rest)))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (nth (Datatypes.S k) (p :: rest) real_zero)
                     (real_list_sum nat
                        (fun i : nat => nth i rest real_zero)
                        (seq (Datatypes.S k) (length rest)))
                     (nth k rest real_zero)
                     (real_list_sum Real (fun x : Real => x)
                                   (skipn (Datatypes.S k) rest))).
           ++ apply real_eq_refl.
           ++ exact (IH (Datatypes.S k)).
        -- exact (um_skipn_sum_step k rest).
Qed.

(* 常值表：Σ_{seq 0 n} c == nreal(n)·c *)
Lemma um_seq_const : forall (n : nat) (c : Real),
  real_eq (real_list_sum nat (fun _ : nat => c) (seq 0 n))
          (real_mult (um_nreal n) c).
Proof.
  induction n as [| n IH]; intro c.
  - cbn [seq um_nreal real_list_sum].
    apply real_eq_sym.
    apply (real_eq_trans (real_mult real_zero c)
             (real_mult c real_zero) real_zero).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - cbn [seq um_nreal real_list_sum].
    (* c + Σ_{seq 1 n} c == c + nreal n·c == (1 + nreal n)·c *)
    apply (real_eq_trans
             (real_plus c
                        (real_list_sum nat (fun _ : nat => c)
                                       (seq (Datatypes.S 0) n)))
             (real_plus c (real_mult (um_nreal n) c))).
    + apply (RealSetoid.real_eq_plus_compat c
                (real_list_sum nat (fun _ : nat => c) (seq 1 n))
                c (real_mult (um_nreal n) c)).
      * apply real_eq_refl.
      * apply (real_eq_trans
                 (real_list_sum nat (fun _ : nat => c) (seq 1 n))
                 (real_list_sum nat (fun _ : nat => c) (seq 0 n))).
        -- exact (um_seq_shift (fun _ : nat => c) n 0).
        -- exact (IH c).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_plus real_one (um_nreal n)) c)
               (real_mult c (real_plus real_one (um_nreal n)))).
      * apply real_mult_comm.
      * apply (real_eq_trans
                 (real_mult c (real_plus real_one (um_nreal n)))
                 (real_plus (real_mult c real_one)
                            (real_mult c (um_nreal n)))).
        -- exact (real_distrib c real_one (um_nreal n)).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult c real_one) (real_mult c (um_nreal n))
                     c (real_mult (um_nreal n) c)).
           ++ apply real_mult_one.
           ++ apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 2. 熵项与 log 单调                                            *)
(* ============================================================ *)

(* 熵项：p·(−log p) *)
Definition um_ent_term (p : Real) (Hp : real_lt real_zero p) : Real :=
  real_mult p (real_opp (cw_log p Hp)).

(* log 单调（≤ 版：由严格版 + real_log_wd 的 Or 分解拼合） *)
Lemma um_log_le_mono : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb Hle. destruct Hle as [Hlt | Heq].
  - apply um_lt_le. exact (real_log_lt_mono a b Ha Hb Hlt).
  - exact (um_eq_le _ _ (real_log_wd a b Ha Hb Heq)).
Qed.

(* 逐项熵项下界：p ≤ M ⟹ p·(−log M) ≤ p·(−log p)
   （log 反单调 + 乘非负权重 p） *)
Lemma um_ent_term_le : forall (p M : Real)
    (Hp : real_lt real_zero p) (HM : real_lt real_zero M),
  real_le p M ->
  real_le (real_mult p (real_opp (cw_log M HM)))
          (real_mult p (real_opp (cw_log p Hp))).
Proof.
  intros p M Hp HM Hle.
  assert (Hlog : real_le (real_opp (cw_log M HM)) (real_opp (cw_log p Hp))).
  { apply real_opp_le_compat.
    apply um_log_le_mono. exact Hle. }
  apply (RealSetoid.real_le_id_l
           (real_mult p (real_opp (cw_log M HM)))
           (real_mult (real_opp (cw_log M HM)) p)
           (real_mult p (real_opp (cw_log p Hp)))).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r
             (real_mult (real_opp (cw_log M HM)) p)
             (real_mult (real_opp (cw_log p Hp)) p)
             (real_mult p (real_opp (cw_log p Hp)))).
    + apply real_mult_comm.
    + exact (real_le_mult_compat_weak (real_opp (cw_log M HM))
                                      (real_opp (cw_log p Hp)) p
               (um_lt_le real_zero p Hp) Hlog).
Qed.

(* ============================================================ *)
(* 3. NatLt 下标制的索引和引理（逐点假设函数，无 Prop 解构）      *)
(*    NatLt i n := Id (i <? n) true（扫描库 Set 层界编码）；      *)
(*    关键转换：NatLt (S i) (S n) ≡ NatLt i n（ltb/leb iota）。   *)
(* ============================================================ *)

(* 索引和的逐点 ≤ *)
Lemma um_rls_le_N : forall (f g : nat -> Real) (n : nat),
  (forall j : nat, NatLt j n -> real_le (f j) (g j)) ->
  real_le (real_list_sum nat f (seq 0 n))
          (real_list_sum nat g (seq 0 n)).
Proof.
  intros f g n. revert f g. induction n as [| n IH]; intros f g Hpt.
  - cbn [seq real_list_sum]. apply real_le_refl.
  - cbn [seq real_list_sum].
    apply real_le_plus_compat.
    + exact (Hpt 0 id_refl).
    + apply (RealSetoid.real_le_compat
                (real_list_sum nat (fun j : nat => f (Datatypes.S j))
                                   (seq 0 n))
                (real_list_sum nat f (seq 1 n))
                (real_list_sum nat (fun j : nat => g (Datatypes.S j))
                                   (seq 0 n))
                (real_list_sum nat g (seq 1 n))).
      * exact (real_eq_sym _ _ (um_seq_shift f n 0)).
      * exact (real_eq_sym _ _ (um_seq_shift g n 0)).
      * apply (IH (fun j : nat => f (Datatypes.S j))
                  (fun j : nat => g (Datatypes.S j))).
        intros j Hj. exact (Hpt (Datatypes.S j) Hj).
Qed.

(* 索引和的非负 *)
Lemma um_rls_nonneg_N : forall (g : nat -> Real) (n : nat),
  (forall j : nat, NatLt j n -> real_le real_zero (g j)) ->
  real_le real_zero (real_list_sum nat g (seq 0 n)).
Proof.
  intros g n. revert g. induction n as [| n IH]; intros g Hnn.
  - cbn [seq real_list_sum]. apply real_le_refl.
  - cbn [seq real_list_sum].
    assert (Htail : real_le real_zero
                      (real_list_sum nat
                         (fun j : nat => g (Datatypes.S j))
                         (seq 0 n))).
    { apply (IH (fun j : nat => g (Datatypes.S j))).
      intros j Hj. exact (Hnn (Datatypes.S j) Hj). }
    assert (Hstep : real_le (real_plus real_zero real_zero)
                       (real_plus (g 0)
                                  (real_list_sum nat
                                     (fun j : nat => g (Datatypes.S j))
                                     (seq 0 n)))).
    { apply real_le_plus_compat.
      - exact (Hnn 0 id_refl).
      - exact Htail. }
    exact (RealSetoid.real_le_compat
              (real_plus real_zero real_zero)
              real_zero
              (real_plus (g 0)
                         (real_list_sum nat
                            (fun j : nat => g (Datatypes.S j))
                            (seq 0 n)))
              (real_plus (g 0) (real_list_sum nat g (seq 1 n)))
              (real_plus_zero real_zero)
              (RealSetoid.real_eq_plus_compat (g 0)
                 (real_list_sum nat
                    (fun j : nat => g (Datatypes.S j)) (seq 0 n))
                 (g 0)
                 (real_list_sum nat g (seq 1 n))
                 (real_eq_refl (g 0))
                 (real_eq_sym _ _ (um_seq_shift g n 0)))
              Hstep).
    (* 尾段 le 已由 Hstep 的 d 分量直接给出 *)
Qed.

(* 单成员 ≤ 全和：NatLt i n ⟹ g i ≤ Σ_{seq 0 n} g（权重逐点非负） *)
Lemma um_rls_single_le_N : forall (g : nat -> Real) (n i : nat),
  NatLt i n ->
  (forall j : nat, NatLt j n -> real_le real_zero (g j)) ->
  real_le (g i) (real_list_sum nat g (seq 0 n)).
Proof.
  intros g n. revert g. induction n as [| n IH]; intros g i Hi Hnn.
  - exfalso. exact (um_Emptyset_false (id_false_true Hi)).
  - cbn [seq real_list_sum]. destruct i as [| i'].
    + (* i = 0：头项即目标项；尾段非负经位移换形 *)
      assert (Ht0 : real_le real_zero
                      (real_list_sum nat
                         (fun j : nat => g (Datatypes.S j))
                         (seq 0 n))).
      { apply (um_rls_nonneg_N (fun j : nat => g (Datatypes.S j)) n).
        intros j Hj. exact (Hnn (Datatypes.S j) Hj). }
      apply um_le_add_l.
      exact (RealSetoid.real_le_compat real_zero real_zero
                (real_list_sum nat
                   (fun j : nat => g (Datatypes.S j)) (seq 0 n))
                (real_list_sum nat g (seq 1 n))
                (real_eq_refl real_zero)
                (real_eq_sym _ _ (um_seq_shift g n 0))
                Ht0).
    + (* i = S i'：IH 于 S i'（NatLt (S i') n ≡ NatLt i' n），
         再沿 um_seq_shift 的 eq 换形到 Σ_{seq 1 n} g，加非负头项 *)
      assert (Htail : real_le (g (Datatypes.S i'))
                         (real_list_sum nat
                            (fun j : nat => g (Datatypes.S j))
                            (seq 0 n))).
      { apply (IH (fun j : nat => g (Datatypes.S j)) i'
                  Hi (fun j Hj => Hnn (Datatypes.S j) Hj)). }
      apply real_le_trans with
        (y := real_list_sum nat (fun j : nat => g (Datatypes.S j))
                                (seq 0 n)).
      * exact Htail.
      * apply (real_le_trans
                 (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0 n))
                 (real_list_sum nat g (seq 1 n))
                 (real_plus (g 0) (real_list_sum nat g (seq 1 n)))).
        -- apply (RealSetoid.real_le_compat
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0 n))
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0 n))
                     (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0 n))
                     (real_list_sum nat g (seq 1 n))
                     (real_eq_refl (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0 n)))
                     (real_eq_sym _ _ (um_seq_shift g n 0))
                     (real_le_refl (real_list_sum nat (fun j : nat => g (Datatypes.S j)) (seq 0 n)))).
        -- apply (um_le_add_r (real_list_sum nat g (seq 1 n)) (g 0)).
           exact (Hnn 0 id_refl).
Qed.

(* ============================================================ *)
(* 4. 世界段：tokens / ratio + 三分判定元（镜像 ord_le_dec）      *)
(* ============================================================ *)

Section UpMinPWorld.

(* 三分判定元：a ≤ b ∨ b < a（Real 层 le/lt 的构造性判定假设） *)
Variable um_trich_probe : forall a b : Real, Or (real_le a b) (real_lt b a).

(* 最大值：fold real_max（nil ↦ 0） *)
Fixpoint um_fmax (l : list Real) : Real :=
  match l with
  | nil => real_zero
  | p :: rest => real_max p (um_fmax rest)
  end.

(* 逐点上界（下标版）：NatLt i (length l) ⟹ nth i l 0 ≤ fold_max l *)
Lemma um_fmax_ge_nth : forall (l : list Real) (i : nat),
  NatLt i (length l) -> real_le (nth i l real_zero) (um_fmax l).
Proof.
  induction l as [| p rest IH]; intros i Hi.
  - (* NatLt i 0 ≡ Id false true *)
    destruct (um_Emptyset_false (id_false_true Hi)).
  - cbn [length um_fmax]. destruct i as [| i'].
    + (* 头元素：p ≤ max p M；NatLt 0 (S n) ≡ id_refl *)
      destruct (um_trich_probe p (um_fmax rest)) as [Hle | Hlt].
      * apply (RealSetoid.real_le_id_r p (um_fmax rest)
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (RealInterfaceEnhancedMod.real_r_max_r_iff p
                       (um_fmax rest) Hle)).
        -- exact Hle.
      * apply (RealSetoid.real_le_id_r p p
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (real_r_max_l_iff p (um_fmax rest)
                       (um_lt_le (um_fmax rest) p Hlt))).
        -- apply real_le_refl.
    + (* 尾元素：nth i' rest 0 ≤ max p M；NatLt (S i') (S n) ≡ NatLt i' n *)
      destruct (um_trich_probe p (um_fmax rest)) as [Hle | Hlt].
      * apply (RealSetoid.real_le_id_r (nth i' rest real_zero)
                                          (um_fmax rest)
                                          (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (RealInterfaceEnhancedMod.real_r_max_r_iff p
                       (um_fmax rest) Hle)).
        -- exact (IH i' Hi).
      * apply (RealSetoid.real_le_id_r (nth i' rest real_zero)
                                          p (real_max p (um_fmax rest))).
        -- exact (real_eq_sym _ _
                    (real_r_max_l_iff p (um_fmax rest)
                       (um_lt_le (um_fmax rest) p Hlt))).
        -- apply um_lt_le.
           exact (real_le_lt_trans (nth i' rest real_zero)
                     (um_fmax rest) p (IH i' Hi) Hlt).
Qed.

(* 可达性（下标版）：非空见证 + 逐项正 ⟹ 最大值在表中取到 *)
Lemma um_fmax_mem_nth : forall (l : list Real),
  (sigT (fun i : nat => NatLt i (length l))) ->
  (forall i : nat,
       NatLt i (length l) -> real_lt real_zero (nth i l real_zero)) ->
  sigT (fun i : nat =>
          prod (NatLt i (length l))
               (real_eq (nth i l real_zero) (um_fmax l))).
Proof.
  induction l as [| p rest IH]; intros [i0 Hi0] Hpos.
  - destruct (um_Emptyset_false (id_false_true Hi0)).
  - destruct rest as [| q rest2].
    + (* 单元素表：um_fmax [p] = real_max p real_zero *)
      destruct (um_trich_probe p real_zero) as [Hle | Hlt].
      * (* p ≤ 0 与 p > 0 矛盾 *)
        destruct (um_Emptyset_false
                    (real_lt_irrefl real_zero
                       (real_lt_eq_lt real_zero p real_zero
                          (Hpos Datatypes.O id_refl)
                          (real_eq_sym real_zero p
                             (real_le_antisym real_zero p
                                (um_lt_le real_zero p
                                   (Hpos Datatypes.O id_refl))
                                Hle))))).
      * (* 0 < p：max p 0 == p（左支胜），见证 i = 0 *)
        exact (existT _ Datatypes.O
                 (pair id_refl
                       (real_eq_sym (real_max p real_zero) p
                          (real_r_max_l_iff p real_zero
                             (um_lt_le real_zero p Hlt))))).
    + (* 尾表非空（构造性见证 0）：可达性传给 IH，max p M 按三分取支 *)
      assert (Hrestnn : sigT (fun i : nat => NatLt i (length (q :: rest2)))).
      { exact (existT _ Datatypes.O id_refl). }
      assert (Hposr : forall i : nat,
                NatLt i (length (q :: rest2)) ->
                real_lt real_zero (nth i (q :: rest2) real_zero)).
      { intros i Hi.
        apply (Hpos (Datatypes.S i)).
        (* NatLt (S i) (S (S m)) ≡ NatLt i (S m)（ltb/leb iota） *)
        exact Hi. }
      specialize (IH Hrestnn Hposr).
      destruct IH as [j [Hjlen Hjeq]].
      destruct (um_trich_probe p (um_fmax (q :: rest2))) as [Hle | Hlt].
      * (* max p M == M ∈ 尾表（右支胜）：见证 S j；
           NatLt (S j) (S (S m)) ≡ NatLt j (S m) ≡ Hjlen *)
        exact (existT _ (Datatypes.S j)
                 (pair Hjlen
                       (real_eq_trans
                          (nth (Datatypes.S j) (p :: q :: rest2) real_zero)
                          (nth j (q :: rest2) real_zero)
                          (real_max p (um_fmax (q :: rest2)))
                          (real_eq_refl (nth j (q :: rest2) real_zero))
                          (real_eq_trans
                             (nth j (q :: rest2) real_zero)
                             (um_fmax (q :: rest2))
                             (real_max p (um_fmax (q :: rest2)))
                             Hjeq
                             (real_eq_sym _ _
                                (RealInterfaceEnhancedMod.real_r_max_r_iff p
                                   (um_fmax (q :: rest2)) Hle)))))).
      * (* M < p：max p M == p（左支胜）：见证 0 *)
        exact (existT _ Datatypes.O
                 (pair id_refl
                       (real_eq_sym (real_max p (um_fmax (q :: rest2))) p
                          (real_r_max_l_iff p (um_fmax (q :: rest2))
                             (um_lt_le (um_fmax (q :: rest2)) p Hlt))))).
Qed.

(* 最大值为正：非空见证 + 逐项正 *)
Lemma um_fmax_pos_nth : forall (l : list Real),
  (sigT (fun i : nat => NatLt i (length l))) ->
  (forall i : nat,
       NatLt i (length l) -> real_lt real_zero (nth i l real_zero)) ->
  real_lt real_zero (um_fmax l).
Proof.
  intros l Hne Hpos.
  destruct (um_fmax_mem_nth l Hne Hpos) as [i [Hi Heq]].
  exact (RealSetoid.real_lt_compat real_zero real_zero
           (nth i l real_zero) (um_fmax l)
           (real_eq_refl real_zero) Heq (Hpos i Hi)).
Qed.

(* ============================================================ *)
(* 5. Min-P 截断世界（tokens + ratio）                           *)
(* ============================================================ *)

Section MinPEntropy.

(* 概率表：非空见证、逐项正（下标有界）、和 = 1 *)
Variable tokens : list Real.
Variable tokens_ne : sigT (fun i : nat => NatLt i (length tokens)).
Variable tokens_pos : forall i : nat,
  real_lt real_zero (nth i tokens real_zero).
Hypothesis tokens_sum :
  real_eq (real_list_sum Real (fun x : Real => x) tokens) real_one.

(* Min-P 阈值比例：0 < ratio ≤ 1 *)
Variable ratio : Real.
Hypothesis ratio_pos : real_lt real_zero ratio.
Hypothesis ratio_le_one : real_le ratio real_one.

(* ---- 核心对象 ---- *)
Definition um_N : nat := length tokens.

Definition um_pmax : Real := um_fmax tokens.

Definition um_Hpmax : real_lt real_zero um_pmax :=
  um_fmax_pos_nth tokens tokens_ne (fun i _ => tokens_pos i).

(* 逐点 k ≤ p_max（下标化） *)
Lemma um_le_pmax : forall i : nat,
  NatLt i um_N -> real_le (nth i tokens real_zero) um_pmax.
Proof.
  intros i Hi. exact (um_fmax_ge_nth tokens i Hi).
Qed.

(* S：源分布的 Shannon 熵（list 离散、下标求和版） *)
Definition um_entropy : Real :=
  real_list_sum nat
    (fun i : nat => um_ent_term (nth i tokens real_zero) (tokens_pos i))
    (seq 0 um_N).

(* Min-P 阈值与保留指示：thr = ratio·p_max；保留者取 k，淘汰者取 0 *)
Definition um_thr : Real := real_mult ratio um_pmax.

Definition um_keepF (p : Real) : Real :=
  match um_trich_probe um_thr p with
  | inl _ => p
  | inr _ => real_zero
  end.

(* 保留质量 / 截断质量：kept = Σ keepF，dropped = 1 − kept（定义性） *)
Definition um_kept : Real :=
  real_list_sum nat (fun i : nat => um_keepF (nth i tokens real_zero))
                (seq 0 um_N).

Lemma um_keepF_nonneg_nth : forall (x : Real) (Hx : real_lt real_zero x),
  real_le real_zero (um_keepF x).
Proof.
  intros x Hx.
  unfold um_keepF.
  destruct (um_trich_probe um_thr x) as [Hkeep | Hdrop].
  - apply um_lt_le. exact Hx.
  - apply real_le_refl.
Qed.

(* 保留权重的逐点非负（下标全域版，供索引和引理使用） *)
Definition um_keepF_nonneg : forall i : nat,
  real_le real_zero (um_keepF (nth i tokens real_zero)) :=
  fun i => um_keepF_nonneg_nth (nth i tokens real_zero) (tokens_pos i).

Definition um_dropped : Real :=
  real_plus real_one (real_opp um_kept).

(* ---- keepF 的代数性质 ---- *)
Lemma um_keepF_congr : forall x y : Real,
  real_eq x y -> real_eq (um_keepF x) (um_keepF y).
Proof.
  intros x y Heq.
  unfold um_keepF.
  destruct (um_trich_probe um_thr x) as [Hx | Hx];
    destruct (um_trich_probe um_thr y) as [Hy | Hy].
  - (* x、y 均保留：keepF x == x == y == keepF y *)
    apply Heq.
  - (* x 保留、y 淘汰：y < thr ⟹ x < thr（换形）与 thr ≤ x 矛盾 *)
    destruct (um_Emptyset_false (real_lt_irrefl x
                (real_lt_le_trans x um_thr x
                   (RealSetoid.real_lt_compat y x um_thr um_thr
                      (real_eq_sym x y Heq) (real_eq_refl um_thr) Hy)
                   Hx))).
  - (* x 淘汰、y 保留：thr ≤ y ⟹ thr ≤ x（换形）与 x < thr 矛盾 *)
    destruct (um_Emptyset_false (real_lt_irrefl um_thr
                (real_le_lt_trans um_thr x um_thr
                   (RealSetoid.real_le_compat um_thr um_thr y x
                      (real_eq_refl um_thr) (real_eq_sym x y Heq) Hy)
                   Hx))).
  - (* 均淘汰：0 == 0 *)
    apply real_eq_refl.
Qed.


(* thr ≤ p_max：ratio·p_max ≤ 1·p_max == p_max *)
Lemma um_thr_le_pmax : real_le um_thr um_pmax.
Proof.
  apply (RealSetoid.real_le_id_r (real_mult ratio um_pmax)
                                 (real_mult real_one um_pmax) um_pmax).
  - apply um_mult_one_l.
  - exact (real_le_mult_compat_weak ratio real_one um_pmax
             (um_lt_le real_zero um_pmax um_Hpmax) ratio_le_one).
Qed.

(* ============================================================ *)
(* 件 1：S ≥ −log(p_max)                                        *)
(* ============================================================ *)

Theorem entropy_ge_neg_log_p_max :
  real_le (real_opp (cw_log um_pmax um_Hpmax)) um_entropy.
Proof.
  apply real_le_trans with
    (y := real_list_sum nat
            (fun i : nat =>
               real_mult (nth i tokens real_zero)
                         (real_opp (cw_log um_pmax um_Hpmax)))
            (seq 0 um_N)).
  - (* (−log p_max) == (−log p_max)·Σ nth == (−log p_max)·1
       （反向即 Σ nth·(−log p_max)） *)
    apply um_eq_le.
    apply (real_eq_trans
             (real_opp (cw_log um_pmax um_Hpmax))
             (real_mult (real_opp (cw_log um_pmax um_Hpmax))
                        (real_list_sum nat
                           (fun i : nat => nth i tokens real_zero)
                           (seq 0 um_N)))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_mult (real_opp (cw_log um_pmax um_Hpmax))
                          (real_list_sum nat
                             (fun i : nat => nth i tokens real_zero)
                             (seq 0 um_N)))
               (real_mult (real_opp (cw_log um_pmax um_Hpmax)) real_one)).
      * apply (RealSetoid.real_eq_mult_compat
                  (real_opp (cw_log um_pmax um_Hpmax))
                  (real_list_sum nat
                     (fun i : nat => nth i tokens real_zero)
                     (seq 0 um_N))
                  (real_opp (cw_log um_pmax um_Hpmax)) real_one).
        -- apply real_eq_refl.
        -- (* Σ_{seq 0 N} nth i tokens 0 == 1 *)
           apply (real_eq_trans
                    (real_list_sum nat
                       (fun i : nat => nth i tokens real_zero)
                       (seq 0 (length tokens)))
                    (real_list_sum Real (fun x : Real => x) tokens)).
           ++ exact (um_seq_nth_sum tokens 0).
           ++ exact tokens_sum.
      * apply real_mult_one.
    + apply real_eq_sym.
      exact (real_list_sum_linear_r nat
               (real_opp (cw_log um_pmax um_Hpmax))
               (fun i : nat => nth i tokens real_zero) (seq 0 um_N)).
  - (* 逐项：nth i tokens 0 ≤ p_max ⟹ nth·(−log p_max) ≤ 熵项 *)
    apply (um_rls_le_N
              (fun i : nat =>
                 real_mult (nth i tokens real_zero)
                           (real_opp (cw_log um_pmax um_Hpmax)))
              (fun i : nat =>
                 um_ent_term (nth i tokens real_zero) (tokens_pos i))
              um_N).
    intros j Hj.
    exact (um_ent_term_le (nth j tokens real_zero) um_pmax
              (tokens_pos j) um_Hpmax (um_le_pmax j Hj)).
Qed.

(* pick_max 必被保留：kept ≥ p_max *)
Lemma um_kept_ge_pmax : real_le um_pmax um_kept.
Proof.
  destruct (um_fmax_mem_nth tokens tokens_ne (fun i _ => tokens_pos i))
    as [istar [Hiistar Heqstar]].
  apply (RealSetoid.real_le_id_l um_pmax
            (um_keepF (nth istar tokens real_zero)) um_kept).
  - (* eq um_pmax (keepF (nth istar))：p_max 被保留 ⟹ keepF um_pmax == um_pmax，
       再沿 congruence 换形到 keepF (nth istar) *)
    apply (real_eq_trans um_pmax (um_keepF um_pmax)
             (um_keepF (nth istar tokens real_zero))).
    + unfold um_keepF.
      destruct (um_trich_probe um_thr um_pmax) as [Hkeep | Hdrop].
      * apply real_eq_refl.
      * exact (False_rect _
                 (um_Emptyset_false
                    (real_lt_irrefl um_pmax
                       (real_lt_le_trans um_pmax um_thr um_pmax Hdrop
                                          um_thr_le_pmax)))).
    + exact (um_keepF_congr um_pmax (nth istar tokens real_zero)
               (real_eq_sym _ _ Heqstar)).
  - (* 单成员 ≤ 全和：keepF (nth istar) ≤ Σ keepF *)
    exact (um_rls_single_le_N
              (fun i : nat => um_keepF (nth i tokens real_zero))
              um_N istar Hiistar (fun j _ => um_keepF_nonneg j)).
Qed.

(* e^{−S} ≤ p_max：S ≥ −log p_max ⟹ exp antitone ⟹
   e^{−S} ≤ e^{−(−log p_max)} == e^{log p_max} == p_max *)
Lemma um_exp_neg_S_le_pmax :
  real_le (real_exp_neg um_entropy) um_pmax.
Proof.
  apply (RealSetoid.real_le_id_r (real_exp_neg um_entropy)
            (real_exp_neg (real_opp (cw_log um_pmax um_Hpmax))) um_pmax).
  - (* e^{−(−log p_max)} == p_max *)
    exact (real_exp_neg_log_inv um_pmax um_Hpmax).
  - apply real_exp_neg_le_decr.
    exact entropy_ge_neg_log_p_max.
Qed.

(* ============================================================ *)
(* 件 2：dropped ≤ 1 − e^{−S}                                   *)
(* ============================================================ *)

Theorem dropped_le_one_minus_exp_neg_S :
  real_le um_dropped
          (real_plus real_one (real_opp (real_exp_neg um_entropy))).
Proof.
  unfold um_dropped.
  apply real_le_plus_compat.
  - apply real_le_refl.
  - apply real_opp_le_compat.
    apply real_le_trans with (y := um_pmax).
    + exact um_exp_neg_S_le_pmax.
    + exact um_kept_ge_pmax.
Qed.

(* ============================================================ *)
(* 件 3：dropped ≤ 1 − 1/N（N = |tokens|；均匀特例）             *)
(* ============================================================ *)

Definition um_Npos : real_lt real_zero (um_nreal um_N).
Proof.
  destruct tokens_ne as [i Hi].
  exact (um_nreal_pos_of_lt um_N i Hi).
Defined.

(* p_max ≥ 1/N：Σk = 1 ≤ N·p_max ⟹ inv N ≤ p_max
   （反证：p_max < inv N ⟹ N·p_max < N·inv N == 1，矛盾） *)
Lemma um_pmax_ge_inv_n :
  real_le (real_inv_pos (um_nreal um_N) um_Npos) um_pmax.
Proof.
  assert (H1 : real_le real_one
                 (real_mult (um_nreal um_N) um_pmax)).
  { (* 1 == Σnth ≤ Σ(const p_max) == N·p_max *)
    apply real_le_trans with
      (y := real_list_sum nat
              (fun i : nat => nth i tokens real_zero) (seq 0 um_N)).
    - apply um_eq_le.
      apply (real_eq_trans real_one
               (real_list_sum Real (fun x : Real => x) tokens)
               (real_list_sum nat
                  (fun i : nat => nth i tokens real_zero) (seq 0 um_N))).
      * exact (real_eq_sym _ _ tokens_sum).
      * exact (real_eq_sym _ _ (um_seq_nth_sum tokens 0)).
    - apply real_le_trans with
        (y := real_list_sum nat (fun _ : nat => um_pmax) (seq 0 um_N)).
      + apply (um_rls_le_N (fun i : nat => nth i tokens real_zero)
                 (fun _ : nat => um_pmax) um_N).
        intros j Hj. apply um_le_pmax. exact Hj.
      + apply um_eq_le. exact (um_seq_const um_N um_pmax). }
  destruct (um_trich_probe (real_inv_pos (um_nreal um_N) um_Npos)
                           um_pmax) as [Hle | Hlt].
  - exact Hle.
  - destruct (um_Emptyset_false
                (real_lt_irrefl real_one
                   (real_le_lt_trans real_one
                      (real_mult (um_nreal um_N) um_pmax) real_one H1
                      (real_lt_eq_lt
                         (real_mult (um_nreal um_N) um_pmax)
                         (real_mult (um_nreal um_N)
                                    (real_inv_pos (um_nreal um_N) um_Npos))
                         real_one
                         (real_lt_mult_compat um_pmax
                            (real_inv_pos (um_nreal um_N) um_Npos)
                            (um_nreal um_N) um_Npos Hlt)
                         (real_inv_pos_correct (um_nreal um_N) um_Npos))))).
Qed.

Theorem dropped_le_one_minus_inv_n :
  real_le um_dropped
          (real_plus real_one
                (real_opp (real_inv_pos (um_nreal um_N) um_Npos))).
Proof.
  unfold um_dropped.
  apply real_le_plus_compat.
  - apply real_le_refl.
  - apply real_opp_le_compat.
    apply real_le_trans with (y := um_pmax).
    + exact um_pmax_ge_inv_n.
    + exact um_kept_ge_pmax.
Qed.

End MinPEntropy.

End UpMinPWorld.

Local Close Scope nat_scope.

(* ---------- UpAlignId ---------- *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* ============================================================ *)
(* UpAlignId.v —— 对齐递减恒等式件（王中王批拆分件：热点 A5/B2）      *)
(*                                                                *)
(* 使命：把根内 Section Alignment 策略迭代的"单调 ≤"升级为"精确恒等式"。*)
(*   升级源：L23086 policy_iter_gap_mono（gap_{t+1} ≤ gap_t）与        *)
(*   L23244 dpo_loss_iter_step_le（loss 单步 ≤）均只有定性信息。       *)
(*                                                                *)
(* 数学目标（纸笔推导后的最终恒等式全文；记 J(p) := align_objective p，  *)
(*   gap(p) := J(pi_star) − J(p)，pi_{t+1} := pi_next pi_t，            *)
(*   K1 := KL(pi_{t+1}‖pi_t)，K2 := KL(pi_t‖pi_{t+1})，                 *)
(*   Δ := β·[(1/η−1)·K1 + (1/η)·K2]）：                                *)
(*                                                                *)
(*   件 A policy_gap_next_exact（gap 的单步精确分解）：              *)
(*     gap(pi_{t+1}) == gap(pi_t) − Δ                              *)
(*     即 J* − J(pi_{t+1})                                          *)
(*        == β·KL(pi_t‖pi_star) − β·[(1/η−1)·K1 + (1/η)·K2]。           *)
(*   件 A' policy_gap_decrement_exact（单调 ≤ 的精确化）：           *)
(*     gap(pi_t) − gap(pi_{t+1}) == Δ（每步下降量的精确值）。        *)
(*   件 B dpo_loss_step_exact（dpo_loss := opp J，换轴并列形态）：    *)
(*     dpo_loss(pi_t) − dpo_loss(pi_{t+1}) == Δ。                   *)
(*   伴随件 C policy_gap_backward_kl_exact（L22686 换轴组装）：       *)
(*     β·KL(pi*‖pi_{t+1})                                           *)
(*       == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2，              *)
(*     中项 gap(pi_t) 即 L20554 前向间隙——后向 KL 单步递推以前向      *)
(*     gap 精确进入（恒等式层面的两轴桥；前向/后向 KL 的"比较"仍需    *)
(*     Pinsker 型传递，库内无此材料，见扫描报告构造性边界 #1）。      *)
(*                                                                *)
(* 装配机器（全部在根，零新建分析机器）：                            *)
(*   L20554 rlhf_suboptimality_gap：gap(p) == β·KL(p‖pi_star)；           *)
(*   L23000 policy_iter_gap_diff：J(pi_{t+1}) − J(pi_t) == Δ；        *)
(*   L22686 policy_iter_backward_kl_step：三 KL 精确恒等（除 β 版）； *)
(*   差分代数：根内 minus_minus_distr + minus_plus_cancel（望远镜）    *)
(*   与 minus_rearrange_four + minus_self_zero + opp_minus（左消去）， *)
(*   本文件封装为 minus_middle_t12 / minus_left_cancel_t12 两件。     *)
(*                                                                *)
(* 诚实注记：扫描报告 A5 草案 RHS（η·KL(pi_t‖pi_star) − KL(pi_t‖pi_{t+1})，  *)
(*   无 β）混轴且丢 β 因子，作为恒等式不可由 L20554/L22686 推出；      *)
(*   本件按"两引理代数操作合并为准"落为上列可证形态。                *)
(*                                                                *)
(* 红线自审：纯构造性（零公理/零弃证/零经典逻辑，库 Not 为 Set 层      *)
(*   A -> Empty_set 编码）；语句全为 Set 层（premise 全为 lt/Id，      *)
(*   无 Prop 前提）；全部 Qed；尾部 Extraction 探针验证可提取性。      *)
(* ============================================================ *)


(* ---------- 镜像 Section Alignment 的声明（同名同序；未用不声明） ---------- *)

Section AlignIdWorld.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* 奖励函数 r(s) *)
Variable beta : R.                 (* KL 正则化温度 β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* 参考策略 *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align reward beta beta_pos pi_ref).
Variable eta : R.                  (* 镜像步长 η > 0 *)
Variable eta_pos : lt zero eta.
Variable sum_over_S_pos : forall (f : S -> R),
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

(* ---------- 差分代数封装（根内机器两步装配，供两主件共用） ---------- *)

(* 望远镜：已知 b 的公共项抽取。
   (a − b) − (c − b) == a − c
   装配：minus_minus_distr（(a−b)−c == a−(b+c)，根内 L19183）
       + minus_plus_cancel（b + (c−b) == c，根内 L668）。 *)
Lemma minus_middle_t12 : forall a b c : R,
  Id (minus (minus a b) (minus c b)) (minus a c).
Proof.
  intros a b c.
  exact (id_trans (minus_minus_distr a b (minus c b))
                  (id_cong (fun x => minus a x) (minus_plus_cancel b c))).
Qed.

(* 左消去：(a − b) − (a − c) == c − b（gap 下降量的换形核）。
   装配：minus_rearrange_four（根内 L19773，四元差分重排）
       + minus_self_zero（a − a == 0，根内 L984）
       + minus zero X == opp X（plus_comm/plus_zero）
       + opp_minus（根内 L706）+ plus_comm。 *)
Lemma minus_left_cancel_t12 : forall a b c : R,
  Id (minus (minus a b) (minus a c)) (minus c b).
Proof.
  intros a b c.
  assert (Hzero : Id (minus zero (minus b c)) (minus c b)).
  {
    assert (H1 : Id (minus zero (minus b c)) (opp (minus b c)))
      by exact (id_trans (plus_comm zero (opp (minus b c)))
                         (plus_zero (opp (minus b c)))).
    assert (H2 : Id (opp (minus b c)) (minus c b))
      by exact (id_trans (opp_minus b c) (plus_comm (opp b) c)).
    exact (id_trans H1 H2).
  }
  exact (id_trans (minus_rearrange_four a b a c)
                  (id_trans (id_cong2 minus (minus_self_zero a a id_refl) id_refl)
                            Hzero)).
Qed.

(* ---------- 件 A：次优间隙的单步精确分解恒等式 ---------- *)
(* gap(pi_{t+1}) == gap(pi_t) − β·[(1/η−1)·K1 + (1/η)·K2]
   装配 = 恒等式 + 恒等式 = 恒等式：
     gap(pi_t) == β·KL(pi_t‖pi_star)       （L20554）
     J(pi_{t+1}) − J(pi_t) == Δ              （L23000）
     望远镜：J* − J(pi_{t+1}) == (J* − J(pi_t)) − (J(pi_{t+1}) − J(pi_t))。 *)
Theorem policy_gap_next_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (align_objective reward beta pi_ref
                 (pi_star reward beta beta_pos pi_ref Z_align_pos))
              (align_objective reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (minus (mult beta (relative_entropy pi_t
                 (pi_star reward beta beta_pos pi_ref Z_align_pos)))
              (mult beta (plus
                 (mult (minus (inv_pos eta eta_pos) one)
                       (relative_entropy (pi_next reward beta beta_pos pi_ref
                                            eta sum_over_S_pos pi_t pi_t_pos)
                                         pi_t))
                 (mult (inv_pos eta eta_pos)
                       (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos)))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (id_sym (minus_middle_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np)))
           (id_cong2 minus Hgap Hdiff)).
Qed.

(* ---------- 件 A'：gap 递减量的精确恒等式（L23086 单调 ≤ 的精确化） ---------- *)
(* gap(pi_t) − gap(pi_{t+1}) == Δ；右端两 KL 均非负（根内 KL 机器），
   故单调 ≤ 为本恒等式的直接读出，且带精确步长。 *)
Corollary policy_gap_decrement_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref pi_t))
              (minus (align_objective reward beta pi_ref
                        (pi_star reward beta beta_pos pi_ref Z_align_pos))
                     (align_objective reward beta pi_ref
                        (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                           pi_t pi_t_pos))))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_left_cancel_t12
             (align_objective reward beta pi_ref Ps)
             (align_objective reward beta pi_ref pi_t)
             (align_objective reward beta pi_ref Np))
           Hdiff).
Qed.

(* ---------- 件 B：dpo_loss 单步精确差恒等式（换轴并列形态） ---------- *)
(* dpo_loss(pi) := opp (align_objective pi)（根内 L19090）。
   dpo_loss(pi_t) − dpo_loss(pi_{t+1}) == Δ。
   与根内 L23000 policy_iter_gap_diff 的关系：换轴并列——L23000 是 J 轴
   单步改进量，本件是 loss 轴单步下降量，二者经 minus_opp_opp 精确互逆
   （对偶轴上的显式陈述，供损失动态叙事直接引用）。 *)
Theorem dpo_loss_step_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (minus (dpo_loss reward beta pi_ref pi_t)
              (dpo_loss reward beta pi_ref
                 (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                    pi_t pi_t_pos)))
       (mult beta (plus
          (mult (minus (inv_pos eta eta_pos) one)
                (relative_entropy (pi_next reward beta beta_pos pi_ref eta
                                     sum_over_S_pos pi_t pi_t_pos)
                                  pi_t))
          (mult (inv_pos eta eta_pos)
                (relative_entropy pi_t
                   (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                      pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  unfold dpo_loss.
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hdiff : Id (minus (align_objective reward beta pi_ref Np)
                            (align_objective reward beta pi_ref pi_t))
                     (mult beta (plus
                        (mult (minus (inv_pos eta eta_pos) one)
                              (relative_entropy Np pi_t))
                        (mult (inv_pos eta eta_pos)
                              (relative_entropy pi_t Np)))))
    by exact (policy_iter_gap_diff reward beta beta_pos pi_ref eta eta_pos
                                   sum_over_S_pos pi_t pi_t_pos pi_t_norm).
  exact (id_trans (minus_opp_opp (align_objective reward beta pi_ref pi_t)
                                 (align_objective reward beta pi_ref Np))
                  Hdiff).
Qed.

(* ---------- 伴随件 C：后向 KL 递推的换轴精确恒等式 ---------- *)
(* β·KL(pi*‖pi_{t+1}) == (1−η)·β·KL(pi*‖pi_t) − η·gap(pi_t) + β·K2
   装配 = L22686（三 KL 恒等，除 β 版）整体乘 β（distrib + mult 交换
   吸收）+ 中项以 L20554 的 gap(pi_t) = J* − J(pi_t) 精确代换。
   定量解读：后向 KL 每步恰降 η·gap(pi_t)，并被前向步长 KL(β·K2) 抵消。 *)
Theorem policy_gap_backward_kl_exact :
  forall (pi_t : S -> R) (pi_t_pos : forall s : S, lt zero (pi_t s))
         (pi_t_norm : Id (sum_over_S pi_t) one),
    Id (mult beta (relative_entropy
             (pi_star reward beta beta_pos pi_ref Z_align_pos)
             (pi_next reward beta beta_pos pi_ref eta sum_over_S_pos
                pi_t pi_t_pos)))
       (plus (mult (minus one eta)
                   (mult beta (relative_entropy
                          (pi_star reward beta beta_pos pi_ref Z_align_pos)
                          pi_t)))
             (plus (opp (mult eta
                          (minus (align_objective reward beta pi_ref
                                    (pi_star reward beta beta_pos pi_ref
                                       Z_align_pos))
                                 (align_objective reward beta pi_ref pi_t))))
                   (mult beta (relative_entropy pi_t
                          (pi_next reward beta beta_pos pi_ref eta
                             sum_over_S_pos pi_t pi_t_pos))))).
Proof.
  intros pi_t pi_t_pos pi_t_norm.
  set (Ps := pi_star reward beta beta_pos pi_ref Z_align_pos).
  set (Np := pi_next reward beta beta_pos pi_ref eta sum_over_S_pos pi_t pi_t_pos).
  assert (Hnextpos : forall s : S, lt zero (Np s)).
  {
    intro s. unfold Np.
    exact (pi_next_pos reward beta beta_pos pi_ref eta sum_over_S_pos
                       pi_t pi_t_pos s).
  }
  assert (Hgap : Id (minus (align_objective reward beta pi_ref Ps)
                           (align_objective reward beta pi_ref pi_t))
                     (mult beta (relative_entropy pi_t Ps)))
    by exact (rlhf_suboptimality_gap reward beta beta_pos pi_ref pi_ref_pos
                                     Z_align_pos pi_t pi_t_norm pi_t_pos).
  (* L22686 原始恒等（除 β 版三 KL） *)
  assert (Hb : Id (relative_entropy Ps Np)
                   (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                         (plus (opp (mult eta (relative_entropy pi_t Ps)))
                               (relative_entropy pi_t Np))))
    by exact (policy_iter_backward_kl_step reward beta beta_pos pi_ref
                                           pi_ref_pos Z_align_pos eta eta_pos
                                           sum_over_S_pos pi_t pi_t_pos
                                           pi_t_norm Hnextpos).
  (* β 缩放：β·(k·X) == k·(β·X)（结合-交换-反结合三步） *)
  assert (Hscale1 : Id (mult beta (mult (minus one eta) (relative_entropy Ps pi_t)))
                       (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))).
  {
    apply (id_trans (mult_assoc beta (minus one eta) (relative_entropy Ps pi_t))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy Ps pi_t))
                             (mult_comm beta (minus one eta)))).
    exact (id_sym (mult_assoc (minus one eta) beta (relative_entropy Ps pi_t))).
  }
  assert (Hswap2 : Id (mult beta (mult eta (relative_entropy pi_t Ps)))
                      (mult eta (mult beta (relative_entropy pi_t Ps)))).
  {
    apply (id_trans (mult_assoc beta eta (relative_entropy pi_t Ps))).
    apply (id_trans (id_cong (fun x => mult x (relative_entropy pi_t Ps))
                             (mult_comm beta eta))).
    exact (id_sym (mult_assoc eta beta (relative_entropy pi_t Ps))).
  }
  (* β·(opp (η·KLts)) == opp (η·gap(pi_t))：opp_mult_l + Hswap2 + Hgap 代换 *)
  assert (Hscale2 : Id (mult beta (opp (mult eta (relative_entropy pi_t Ps))))
                       (opp (mult eta
                              (minus (align_objective reward beta pi_ref Ps)
                                     (align_objective reward beta pi_ref pi_t))))).
  {
    apply (id_trans (opp_mult_l beta (mult eta (relative_entropy pi_t Ps)))).
    exact (id_cong opp
                   (id_trans Hswap2
                             (id_cong (fun z => mult eta z) (id_sym Hgap)))).
  }
  (* β 分配到后半树：β·(B + C) == β·B + β·C，B 项换形 *)
  assert (Hscale3 : Id (mult beta (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                        (relative_entropy pi_t Np)))
                       (plus (opp (mult eta
                                    (minus (align_objective reward beta pi_ref Ps)
                                           (align_objective reward beta pi_ref pi_t))))
                             (mult beta (relative_entropy pi_t Np))))
    by exact (id_trans (distrib beta (opp (mult eta (relative_entropy pi_t Ps)))
                                (relative_entropy pi_t Np))
                       (id_cong2 plus Hscale2 id_refl)).
  (* 全树 β 分配组装 *)
  assert (Hscale : Id (mult beta (plus (mult (minus one eta) (relative_entropy Ps pi_t))
                                       (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                             (relative_entropy pi_t Np))))
                       (plus (mult (minus one eta) (mult beta (relative_entropy Ps pi_t)))
                             (plus (opp (mult eta
                                          (minus (align_objective reward beta pi_ref Ps)
                                                 (align_objective reward beta pi_ref pi_t))))
                                   (mult beta (relative_entropy pi_t Np)))))
    by exact (id_trans (distrib beta (mult (minus one eta) (relative_entropy Ps pi_t))
                                (plus (opp (mult eta (relative_entropy pi_t Ps)))
                                      (relative_entropy pi_t Np)))
                       (id_cong2 plus Hscale1 Hscale3)).
  exact (id_trans (id_cong (mult beta) Hb) Hscale).
Qed.

End AlignIdWorld.

(* ---------- 提取探针（G3：Obj.magic = 0） ---------- *)

Extraction "alignid.ml" policy_gap_next_exact policy_gap_decrement_exact
  dpo_loss_step_exact policy_gap_backward_kl_exact.

(* ---------- UpProj ---------- *)
(* ============================================================ *)
(* UpProj.v — 四象归一：抽象投影核母定理（Real 层 list 世界）      *)
(*                                                              *)
(*   三象 grep 实证定义同构（KV 逐出 / 安全过滤 / Min-P 截断），    *)
(*   本文件提取母定理并回接三象实例：                             *)
(*     母签名：I（索引）、f（被投影权重）、P（bool 保留谓词）、     *)
(*     idx（枚举）、f_norm（f 归一化）、f_pos（f 逐点正）、        *)
(*     P_witness（保留集非空见证 sigT——ZP_pos 由之升级为定理）。   *)
(*   件 0 ZP_le_one / 件 1 proj_normalized / 件 2 proj_keep_ge    *)
(*   件 3 proj_drop_zero / 件 4 proj_kl_cost（代价恒等·主件）      *)
(*   件 5 proj_minor_uncond（minorization 传送）/ 件 6            *)
(*   proj_uniform_full（P≡true 退化象 = 温度极限象的推论级连接）。  *)
(*                                                              *)
(*   全部 Set 层（Id/And/Or/sigT），语句零 Prop 泄露；            *)
(*   纯构造性：仅依赖 CW_ConstructiveWorld_219，无外部假设。       *)
(*   日志证书形态：real_log 正性证书随身（keep_form_pos 透明       *)
(*   Definition，对齐 UpAuditBridge 透明证书纪律）。              *)
(* ============================================================ *)


(* ---------- 通用助推（Set 层，规避根内 match-Hin 污染源） ---------- *)
(* Id 沿 Bool 的双子目标投影（UpKVEv kvev_id_transport 先例：       *)
(* 规避 destruct-eqn 对前提的静默代换）。                           *)
Lemma projp_id_transport : forall (A : Set) (x y : A) (M : A -> Set),
  M x -> Id x y -> M y.
Proof.
  intros A x y M m H. exact (match H with id_refl => m end).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进证明项——       *)
(* 根内 single_le_sum_aux 的空 match 提取会产生魔力包装，不复用）。  *)
Lemma projp_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

(* ---------- 基础代数（real_eq 层小工具） ---------- *)

Lemma projp_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

Lemma projp_plus_zero_opp : forall a : Real, real_eq (real_plus (real_opp a) a) real_zero.
Proof.
  intro a. apply (real_eq_trans _ (real_plus a (real_opp a)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* a − c == (a − b) + (b − c)（minus_split 的 Real 形态） *)
Lemma projp_minus_split : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c)))) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_opp c) a
             (real_plus (real_opp b) (real_plus b (real_opp c)))
             (real_eq_refl a)
             (real_eq_sym _ _
               (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c)))
                              (real_plus (real_plus (real_opp b) b) (real_opp c))
                              (real_opp c)
                              (real_plus_assoc (real_opp b) b (real_opp c))
                              (real_eq_trans
                                 (real_plus (real_plus (real_opp b) b) (real_opp c))
                                 (real_plus real_zero (real_opp c))
                                 (real_opp c)
                                 (RealSetoid.real_eq_plus_compat
                                    (real_plus (real_opp b) b) (real_opp c)
                                    real_zero (real_opp c)
                                    (projp_plus_zero_opp b) (real_eq_refl _))
                                 (projp_plus_zero_l (real_opp c)))))).
  - apply (real_plus_assoc a (real_opp b) (real_plus b (real_opp c))).
Qed.

(* (x − L) − x == −L（minus_plus_opp 的 Real 形态） *)
Lemma projp_minus_plus_opp : forall x L : Real,
  real_eq (real_plus (real_plus x (real_opp L)) (real_opp x)) (real_opp L).
Proof.
  intros x L.
  exact (real_eq_trans _ _ _
    (real_eq_sym _ _ (real_plus_assoc x (real_opp L) (real_opp x)))
    (real_eq_trans _ _ _
      (RealSetoid.real_eq_plus_compat x (real_plus (real_opp L) (real_opp x))
                                      x (real_plus (real_opp x) (real_opp L))
                                      (real_eq_refl x)
                                      (real_plus_comm (real_opp L) (real_opp x)))
      (real_eq_trans _ _ _
        (real_plus_assoc x (real_opp x) (real_opp L))
        (real_eq_trans _ _ _
          (RealSetoid.real_eq_plus_compat (real_plus x (real_opp x)) (real_opp L)
                                          real_zero (real_opp L)
                                          (real_plus_opp x) (real_eq_refl _))
          (projp_plus_zero_l (real_opp L)))))). 
Qed.

(* log inv == −log x（log_inv_one_inv 的 Real 层形态） *)
Lemma projp_log_inv_neg : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hsum : real_eq (real_plus (real_log x Hx)
                                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                         real_zero).
  { apply (real_eq_trans _ (real_log (real_mult x (real_inv_pos x Hx))
                                     (real_mult_positive x (real_inv_pos x Hx) Hx
                                       (real_inv_pos_pos x Hx))) _).
    - apply (real_eq_sym _ _ (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    - apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      + apply (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                 (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))
                 real_lt_zero_one (real_inv_pos_correct x Hx)).
      + apply (real_log_one real_lt_zero_one). }
  assert (Hdir : real_eq (real_opp (real_log x Hx))
                         (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  { apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    - apply (real_eq_sym _ _ (real_plus_zero (real_opp (real_log x Hx)))).
    - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx))
                                        (real_plus (real_log x Hx)
                                                   (real_log (real_inv_pos x Hx)
                                                             (real_inv_pos_pos x Hx)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log x Hx)) real_zero
                 (real_opp (real_log x Hx))
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 (real_eq_refl _)
                 (real_eq_sym (real_plus (real_log x Hx)
                                         (real_log (real_inv_pos x Hx)
                                                   (real_inv_pos_pos x Hx)))
                              real_zero Hsum)).
      + apply (real_eq_trans _
                 (real_plus (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
        * apply (real_plus_assoc (real_opp (real_log x Hx)) (real_log x Hx)
                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
        * apply (real_eq_trans _ (real_plus real_zero
                                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
          -- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                       (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       real_zero (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       (projp_plus_zero_opp (real_log x Hx)) (real_eq_refl _)).
          -- apply projp_plus_zero_l. }
  apply (real_eq_sym _ _ Hdir).
Qed.

(* ============================================================ *)
(* 母 Section：抽象投影核（四象归一的规范形）                      *)
(*   Z_P = 保留质量；Proj = 保留支 f·inv(Z_P)、逐出支零。          *)
(* ============================================================ *)
Section AbstractProjection.

Variable I : Set.                          (* 索引类型 *)
Variable f : I -> Real.                    (* 被投影权重 *)
Variable P : I -> bool.                    (* 保留谓词 *)
Variable idx : list I.                     (* 枚举 *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.   (* f 归一化 *)
Variable f_pos : forall i : I, real_lt real_zero (f i).       (* f 逐点正 *)
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

(* 保留质量（三象分母的公共形态：Σ if P then f else 0） *)
Definition Z_P : Real :=
  real_list_sum I (fun i : I => if P i then f i else real_zero) idx.

(* ---------- 件 0a：Z_P > 0（由 P 有点 + f_pos + single_le_sum 放电） ---------- *)
(* UpKVEv Z_keep_pos 同款——ZP_pos 由 Variable 升级为定理。           *)
Lemma Z_P_entry_nonneg : forall (y : I),
  real_le real_zero (if P y then f y else real_zero).
Proof.
  intro y. destruct (P y).
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
Qed.

Theorem ZP_pos : real_lt real_zero Z_P.
Proof.
  destruct P_witness as [i0 [Hk0 Hin0]].
  assert (Hlt0 : real_lt real_zero (if P i0 then f i0 else real_zero)).
  { apply (projp_id_transport bool true (P i0)
             (fun b : bool => real_lt real_zero (if b then f i0 else real_zero))).
    - exact (f_pos i0).
    - exact (id_sym Hk0). }
  assert (Hle : real_le (if P i0 then f i0 else real_zero) Z_P).
  { apply (projp_single_le_sum I
             (fun y : I => if P y then f y else real_zero) i0 idx Hin0).
    intro y. apply Z_P_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Heq).
Qed.

(* ---------- 件 0b：Z_P ≤ 1（保留子集和 ≤ 全和 + f_norm 桥） ---------- *)
Theorem ZP_le_one : real_le Z_P real_one.
Proof.
  apply (real_le_trans _ (real_list_sum I f idx)).
  - apply (real_list_sum_le I
             (fun i : I => if P i then f i else real_zero) f idx).
    intro y. destruct (P y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply f_pos.
  - apply (RealSetoid.real_eq_le _ _). exact f_norm.
Qed.

(* 保留支形态（Proj 的 keep 支；log 证书的载体） *)
Definition keep_form (i : I) : Real :=
  real_mult (f i) (real_inv_pos Z_P ZP_pos).

(* keep 支正性证书（透明 Definition——log 项的随身证书） *)
Definition keep_form_pos (i : I) : real_lt real_zero (keep_form i) :=
  real_mult_positive (f i) (real_inv_pos Z_P ZP_pos)
                     (f_pos i) (real_inv_pos_pos Z_P ZP_pos).

(* 投影核（母形态：if P i then f i·inv(Z_P) else 0） *)
Definition Proj (i : I) : Real :=
  if P i then real_mult (f i) (real_inv_pos Z_P ZP_pos) else real_zero.

(* ---------- 件 3：逐出支归零 ---------- *)
Theorem proj_drop_zero : forall i : I,
  Id (P i) false -> real_eq (Proj i) real_zero.
Proof.
  intros i Hb.
  apply (projp_id_transport bool false (P i)
           (fun b : bool =>
              real_eq (if b then
                         real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hb).
Qed.

(* ---------- keep 支放大器：f i ≤ f i·inv(Z_P)（Z_P ≤ 1 + inv 反单调） ---------- *)
Lemma proj_keep_form_ge : forall i : I,
  real_le (f i) (real_mult (f i) (real_inv_pos Z_P ZP_pos)).
Proof.
  intro i.
  apply (real_le_trans _ (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
  - (* f i == f·inv(1) 的 eq→le 桥 *)
    apply (RealSetoid.real_eq_le (f i)
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (f i) real_one) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos real_one real_lt_zero_one)
                (f i) real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans _
                  (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
        -- apply real_eq_sym. apply b4_one_mult.
        -- apply real_inv_pos_correct.
    + apply real_mult_one.
  - apply (real_le_mult_compat_r (f i)
             (real_inv_pos real_one real_lt_zero_one)
             (real_inv_pos Z_P ZP_pos)).
    + apply real_le_from_lt_aux. apply f_pos.
    + apply (real_inv_pos_le_compat Z_P real_one ZP_pos real_lt_zero_one).
      apply ZP_le_one.
Qed.

(* ---------- 件 2：保留者放大（keep 支 f ≤ Proj） ---------- *)
Theorem proj_keep_ge : forall i : I,
  Id (P i) true -> real_le (f i) (Proj i).
Proof.
  intros i Hb.
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_le (f i)
                (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                 else real_zero))).
  - apply proj_keep_form_ge.
  - exact (id_sym Hb).
Qed.

(* ---------- 件 1：行归一化 Σ Proj == 1 ---------- *)
Theorem proj_normalized :
  real_eq (real_list_sum I (fun i : I => Proj i) idx) real_one.
Proof.
  (* 第一步：逐点改写 Proj 为 g(i)·inv(Z_P)，drop 支经 0·x == 0 归零 *)
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P i then f i else real_zero)
                           (real_inv_pos Z_P ZP_pos))
              idx) _).
  { apply (real_list_sum_ext I (fun i : I => Proj i) _ idx).
    intro y. destruct (P y) eqn:Hk.
    - unfold Proj. rewrite Hk. apply real_eq_refl.
    - unfold Proj. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos Z_P ZP_pos) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* 第二步：linear_r 提取常数 inv(Z_P) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos Z_P ZP_pos) Z_P) _).
  { apply (real_list_sum_linear_r I
             (real_inv_pos Z_P ZP_pos)
             (fun i : I => if P i then f i else real_zero) idx). }
  (* 第三步：inv(Z_P)·Z_P == 1（comm 桥 + real_inv_pos_correct） *)
  apply (real_eq_trans _ (real_mult Z_P (real_inv_pos Z_P ZP_pos)) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- 件 5：minorization 传送（δ·u ≤ f ⟹ δ·u ≤ Proj，无条件式） ---------- *)
Variable u : I -> Real.                    (* 参考分布 *)
Variable delta : Real.
Variable delta_minor : forall i : I,
  real_le (real_mult delta (u i)) (f i).

Theorem proj_minor_uncond : forall i : I,
  real_le (if P i then real_mult delta (u i) else real_zero) (Proj i).
Proof.
  intro i. destruct (P i) eqn:Hk.
  - unfold Proj. rewrite Hk.
    apply (real_le_trans _ (f i)).
    + apply delta_minor.
    + apply proj_keep_form_ge.
  - unfold Proj. rewrite Hk. apply real_le_refl.
Qed.

(* ---------- 件 6：退化象（P ≡ true ⟹ Proj ≡ f；温度极限象的推论级连接） ---------- *)
Theorem proj_uniform_full :
  (forall i : I, Id (P i) true) -> forall i : I, real_eq (Proj i) (f i).
Proof.
  intro P_all. intro i.
  assert (HZ1 : real_eq Z_P real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (P_all y)).
    - exact f_norm. }
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_eq (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 (f i))).
  - apply (real_eq_trans _
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one)) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos Z_P ZP_pos)
                (f i) (real_inv_pos real_one real_lt_zero_one)).
      * apply real_eq_refl.
      * apply (real_inv_pos_ext Z_P real_one ZP_pos real_lt_zero_one HZ1).
    + apply (real_eq_trans _ (real_mult (f i) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                  (f i) (real_inv_pos real_one real_lt_zero_one) (f i) real_one).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _
                      (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
           ++ apply real_eq_sym. apply b4_one_mult.
           ++ apply real_inv_pos_correct.
      * apply real_mult_one.
  - exact (id_sym (P_all i)).
Qed.

End AbstractProjection.

(* ============================================================ *)
(* 件 4：代价恒等（母形态，root kl_sum_split/kl_tail_eval 的       *)
(*   Real 层 list 版）。KL 项按「log 正性证书随身」纪律定义：       *)
(*   对 Proj 的 KL 用掩码形态（keep 支即 keep_form，delta 相等）    *)
(*   规避 drop 支 log 零前提；fail 支由 Hq_fail 归零。             *)
(* ============================================================ *)
Section AbstractKL.

Variable I : Set.
Variable f : I -> Real.
Variable P : I -> bool.
Variable idx : list I.
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

Definition ZK : Real := Z_P I f P idx.
Definition keepK (i : I) : Real := keep_form I f P idx f_pos P_witness i.
Definition keepK_pos (i : I) : real_lt real_zero (keepK i) :=
  keep_form_pos I f P idx f_pos P_witness i.

(* KL 逐项（q‖f：无条件正性；q‖Proj 与尾项：P 掩码形态） *)
Definition KL_f_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  real_mult (q i) (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (f i) (f_pos i)))).
Definition KL_P_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (q i) (Hq i))
                               (real_opp (real_log (keepK i) (keepK_pos i))))
  else real_zero.
Definition KL_T_term (q : I -> Real) (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (keepK i) (keepK_pos i))
                               (real_opp (real_log (f i) (f_pos i))))
  else real_zero.
Definition KL_f_masked (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then KL_f_term q Hq i else real_zero.

Definition KLqf (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_term q Hq) idx.
Definition KLfm (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_masked q Hq) idx.
Definition KLqp (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_P_term q Hq) idx.
Definition KLqt (q : I -> Real) : Real :=
  real_list_sum I (KL_T_term q) idx.

(* 第 1 步：桥——兼容 q 在 drop 支归零后，无掩码和 == 掩码和 *)
Lemma proj_kl_bridge : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqf q Hq) (KLfm q Hq).
Proof.
  intros q Hq Hq_fail.
  apply (real_list_sum_ext I (KL_f_term q Hq) (KL_f_masked q Hq) idx).
  intro y. unfold KL_f_masked. destruct (P y) eqn:Hb.
  - apply real_eq_refl.
  - assert (Hid : Id (P y) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail y Hid) as Hq0.
    apply (real_eq_trans _ (real_mult real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q y)
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               Hq0 (real_eq_refl _)).
    + apply (real_eq_trans _
               (real_mult (real_plus (real_log (q y) (Hq y))
                                     (real_opp (real_log (f y) (f_pos y))))
                          real_zero) _).
      * apply real_mult_comm.
      * apply real_mult_zero.
Qed.

(* 第 2 步：掩码逐点分解（keep 支经 minus_split+distrib；drop 支零和零） *)
Lemma proj_kl_pointwise_split : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)) (i : I),
  real_eq (KL_f_masked q Hq i) (real_plus (KL_P_term q Hq i) (KL_T_term q i)).
Proof.
  intros q Hq i. unfold KL_f_masked, KL_P_term, KL_T_term.
  destruct (P i).
  - apply (real_eq_trans _
             (real_mult (q i)
                (real_plus
                   (real_plus (real_log (q i) (Hq i))
                              (real_opp (real_log (keepK i) (keepK_pos i))))
                   (real_plus (real_log (keepK i) (keepK_pos i))
                              (real_opp (real_log (f i) (f_pos i)))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_plus
                  (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (keepK i) (keepK_pos i))))
                  (real_plus (real_log (keepK i) (keepK_pos i))
                             (real_opp (real_log (f i) (f_pos i)))))
               (real_eq_refl _)
               (projp_minus_split (real_log (q i) (Hq i))
                                  (real_log (keepK i) (keepK_pos i))
                                  (real_log (f i) (f_pos i)))).
    + apply (real_distrib (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (keepK i) (keepK_pos i))))
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))).
  - apply real_eq_sym. apply real_plus_zero.
Qed.

(* 第 3 步：和级分解 Σ(q‖f 掩码) == Σ(q‖Proj) + Σ 尾项 *)
Lemma proj_kl_split_sum : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)),
  real_eq (KLfm q Hq) (real_plus (KLqp q Hq) (KLqt q)).
Proof.
  intros q Hq.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx) _).
  - apply (real_list_sum_ext I (KL_f_masked q Hq)
             (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx).
    exact (proj_kl_pointwise_split q Hq).
  - apply (real_list_sum_add I (KL_P_term q Hq) (KL_T_term q) idx).
Qed.

(* 第 4 步：尾项逐点 == (−log Z_P)·q（keep 支经 log_mult+log_inv_neg；
   drop 支 q 归零两侧归零，照抄根 kl_tail_eval 骨架） *)
Lemma proj_kl_tail_pt : forall (q : I -> Real)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero) (i : I),
  real_eq (KL_T_term q i)
          (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                     (q i)).
Proof.
  intros q Hq_fail i. unfold KL_T_term. destruct (P i) eqn:Hb.
  - assert (HL : real_eq (real_log (keepK i) (keepK_pos i))
                         (real_plus (real_log (f i) (f_pos i))
                                    (real_opp (real_log ZK
                                                (ZP_pos I f P idx f_pos P_witness))))).
    { apply (real_eq_trans _
               (real_log (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                         (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                             (f_pos i)
                                             (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
      - apply (real_log_wd (keepK i)
                 (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (keepK_pos i)
                 (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                     (f_pos i)
                                     (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_eq_refl (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))))).
      - apply (real_eq_trans _
                 (real_plus (real_log (f i) (f_pos i))
                            (real_log (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                      (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
        + apply (real_log_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                   (f_pos i) (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness))).
        + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
                   (projp_log_inv_neg ZK (ZP_pos I f P idx f_pos P_witness))). }
    assert (Hmid : real_eq (real_plus (real_log (keepK i) (keepK_pos i))
                                      (real_opp (real_log (f i) (f_pos i))))
                           (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
    { apply (real_eq_trans _
               (real_plus (real_plus (real_log (f i) (f_pos i))
                                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))))
                          (real_opp (real_log (f i) (f_pos i)))) _).
      - apply (RealSetoid.real_eq_plus_compat _ _ _ _ HL (real_eq_refl _)).
      - apply projp_minus_plus_opp. }
    apply (real_eq_trans _
             (real_mult (q i)
                (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (real_eq_refl _) Hmid).
    + apply real_mult_comm.
  - assert (Hid : Id (P i) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail i Hid) as Hq0.
    apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply (RealSetoid.real_eq_mult_compat
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               real_zero
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (q i) (real_eq_refl _) (real_eq_sym (q i) real_zero Hq0)).
Qed.

(* 第 5 步：尾项求值 Σ 尾 == −log Z_P（ext + linear + 归一化消去） *)
Lemma proj_kl_tail_eval : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqt q) (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))).
Proof.
  intros q Hq_norm Hq_fail.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                      (q i)) idx) _).
  - apply (real_list_sum_ext I (KL_T_term q)
             (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                     (q i)) idx).
    intro w. exact (proj_kl_tail_pt q Hq_fail w).
  - apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        (real_list_sum I q idx)) _).
    + apply (real_list_sum_linear I
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))) q idx).
    + apply (real_eq_trans _
               (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                          real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_list_sum I q idx)
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 real_one (real_eq_refl _) Hq_norm).
      * apply real_mult_one.
Qed.

(* 件 4（主件·代价恒等）：KL(q‖f) == KL(q‖Proj) + (−log Z_P)。
   审计/截断/逐出的信息代价 = 保留质量亏损对数，一次证明三象通用。 *)
Theorem proj_kl_cost : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
   real_eq (KLqf q Hq_pos)
          (real_plus (KLqp q Hq_pos)
                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _ (real_plus (KLqp q Hq_pos) (KLqt q)) _).
  - apply (real_eq_trans _ (KLfm q Hq_pos) _).
    + exact (proj_kl_bridge q Hq_pos Hq_fail).
    + exact (proj_kl_split_sum q Hq_pos).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
             (proj_kl_tail_eval q Hq_norm Hq_fail)).
Qed.

End AbstractKL.

(* ============================================================ *)
(* 实例接入（三象回收）。判据：实例引理证明体短于原证明体。          *)
(* 接缝注记见各 Section 头注释。                                   *)
(* ============================================================ *)

(* ---------- 实例 A：KV 逐出（UpKVEv 的行归一化/件 0/2/2b/3 回收） ----------
   接缝：母签名与 UpKVEv 世界逐参对齐（I:=Tok，f:=K s 固定行，P:=keep）。
   f_norm:=Krow s、f_pos:=Kpos s、P_witness:=keep_nonempty 直通；           *)
Section InstKV.

Variables (Tok : Set) (states : list Tok) (K : Tok -> Tok -> Real)
          (keep : Tok -> bool).
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep_nonempty : sigT (fun s0 : Tok => And (Id (keep s0) true) (InT s0 states)).

Definition Zkv (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.
Definition Kev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Zkv s) (ZP_pos Tok (K s) keep states (Kpos s) keep_nonempty))
  else real_zero.

Theorem kev_Zkv_le_one_via_proj : forall s : Tok, real_le (Zkv s) real_one.
Proof.
  intro s. exact (ZP_le_one Tok (K s) keep states (Krow s) (Kpos s)).
Qed.

Theorem kev_row_normalized_via_proj : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => Kev s s') states) real_one.
Proof.
  intro s. exact (proj_normalized Tok (K s) keep states (Kpos s) keep_nonempty).
Qed.

Theorem kev_drop_zero_via_proj : forall s s' : Tok,
  Id (keep s') false -> real_eq (Kev s s') real_zero.
Proof.
  intros s s' H. exact (proj_drop_zero Tok (K s) keep states (Kpos s) keep_nonempty s' H).
Qed.

Theorem kev_keep_ge_via_proj : forall s s' : Tok,
  Id (keep s') true -> real_le (K s s') (Kev s s').
Proof.
  intros s s' H. exact (proj_keep_ge Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty s' H).
Qed.

Variables (Ukv : Tok -> Real) (deltakv : Real).
Variable delta_minor_kv : forall s s' : Tok,
  real_le (real_mult deltakv (Ukv s')) (K s s').

Theorem kev_minor_uncond_via_proj : forall s s' : Tok,
  real_le (if keep s' then real_mult deltakv (Ukv s') else real_zero) (Kev s s').
Proof.
  intros s s'.
  exact (proj_minor_uncond Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty
                           Ukv deltakv (delta_minor_kv s) s').
Qed.

End InstKV.

(* ---------- 实例 B：安全过滤（根 KLProjection 的 Real 层重述） ----------
   接缝：根 projected_normalized 在接口 R 层（sum_over_S/StateSpace），
   本实例按母定理在 Real-list 层同形重述（Z_aud/投影分布/归一化三件
   同构）；根侧接缝留接口实例化，不在此桥。                             *)
Section InstAudit.

Variables (St : Set) (states : list St) (p : St -> Real) (post_aud : St -> bool).
Variable p_norm : real_eq (real_list_sum St p states) real_one.
Variable p_pos : forall s : St, real_lt real_zero (p s).
Variable aud_witness : sigT (fun s : St => And (Id (post_aud s) true) (InT s states)).

Definition ZaudP : Real :=
  real_list_sum St (fun s : St => if post_aud s then p s else real_zero) states.
Definition proj_dist (s : St) : Real :=
  if post_aud s then
    real_mult (p s) (real_inv_pos ZaudP (ZP_pos St p post_aud states p_pos aud_witness))
  else real_zero.

Theorem Zaud_le_one_via_proj : real_le ZaudP real_one.
Proof.
  exact (ZP_le_one St p post_aud states p_norm p_pos).
Qed.

Theorem projected_normalized_via_proj :
  real_eq (real_list_sum St (fun s : St => proj_dist s) states) real_one.
Proof.
  exact (proj_normalized St p post_aud states p_pos aud_witness).
Qed.

Theorem projected_drop_zero_via_proj : forall s : St,
  Id (post_aud s) false -> real_eq (proj_dist s) real_zero.
Proof.
  intros s H. exact (proj_drop_zero St p post_aud states p_pos aud_witness s H).
Qed.

Theorem projected_keep_ge_via_proj : forall s : St,
  Id (post_aud s) true -> real_le (p s) (proj_dist s).
Proof.
  intros s H. exact (proj_keep_ge St p post_aud states p_norm p_pos aud_witness s H).
Qed.

End InstAudit.

(* ---------- 实例 C：Min-P（Set 载体重述 real_minp_markov_kernel） ----------
   接缝：根 RealMinPMain 的保留谓词是 Set 层命题+Or 判定器（非 bool）。
   本实例经 minp_bool（判定器的 bool 载体，构造性合法）接入母定理，
   再以 ext + inv_ext 双桥回收 match 形核的归一化；root Token:Type 与
   本席 Set 载体的差异为纯载体泛化（内容逐字同构）。                     *)
Section InstMinP.

Variables (W : Set) (vocab : list W).
Variable tf : W -> Real.
Variable tf_norm : real_eq (real_list_sum W tf vocab) real_one.
Variable tf_pos : forall w : W, real_lt real_zero (tf w).
(* 忠实镜像根 RealMinPMain 的判定接口（Set 谓词 + Or 判定器，非 bool） *)
Variable Kw : W -> Set.
Variable keep_dec : forall w : W, Or (Kw w) (Not (Kw w)).

Definition minp_bool (w : W) : bool :=
  match keep_dec w with inl _ => true | inr _ => false end.
Definition temp_sum : Real :=
  real_list_sum W
    (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end) vocab.
Variable temp_sum_pos : real_lt real_zero temp_sum.
(* 母形态见证（对应 root pick_max witness + in-vocab；root 侧非平凡部分
   已由 pick_max_token_minp_keep/pick_best_in_vocab' 证毕，此处为诚实接口） *)
Variable kept_witness : sigT (fun w : W => And (Id (minp_bool w) true) (InT w vocab)).

Definition minp_kernel (w : W) : Real :=
  match keep_dec w with
  | inl _ => real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
  | inr _ => real_zero
  end.

Theorem minp_normalized_via_proj :
  real_eq (real_list_sum W (fun w : W => minp_kernel w) vocab) real_one.
Proof.
  pose proof (proj_normalized W tf minp_bool vocab tf_pos kept_witness) as HP.
  assert (HZeq : real_eq (Z_P W tf minp_bool vocab) temp_sum).
  { apply (real_list_sum_ext W (fun w : W => if minp_bool w then tf w else real_zero)
             (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end)
             vocab).
    intro w. unfold minp_bool. destruct (keep_dec w) as [Hk | Hd].
    - apply real_eq_refl.
    - apply real_eq_refl. }
  apply (real_eq_trans _
           (real_list_sum W
              (fun w : W => if minp_bool w then
                              real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                            else real_zero) vocab) _).
  - apply (real_list_sum_ext W (fun w : W => minp_kernel w) _ vocab).
    intro w. unfold minp_kernel, minp_bool. destruct (keep_dec w) as [Hk | Hd].
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _
             (real_list_sum W
                (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab) _).
    + apply (real_list_sum_ext W
               (fun w : W => if minp_bool w then
                               real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                             else real_zero)
               (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab).
      intro w. unfold minp_bool, Proj. destruct (keep_dec w) as [Hk | Hd].
      * apply (RealSetoid.real_eq_mult_compat (tf w)
                 (real_inv_pos temp_sum temp_sum_pos)
                 (tf w)
                 (real_inv_pos (Z_P W tf minp_bool vocab)
                               (ZP_pos W tf minp_bool vocab tf_pos kept_witness))).
      -- apply real_eq_refl.
      -- apply (real_inv_pos_ext temp_sum (Z_P W tf minp_bool vocab)
                   temp_sum_pos (ZP_pos W tf minp_bool vocab tf_pos kept_witness)
                   (real_eq_sym (Z_P W tf minp_bool vocab) temp_sum HZeq)).
      * apply real_eq_refl.
    + exact HP.
Qed.

End InstMinP.

(* ---------- UpFirewall ---------- *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* ============================================================
   UpFirewall.v —— 熵防火墙：退化检测与恢复的构造性闭环
   （外推推导 4；上游三段：UpEntropyGain 记账 + UpBudgetReal 击穿
     + UpTempWindow 恢复窗口；本件补齐温度-熵单调这块承重板）

   纸笔推导（先于动手，完整链）：
     连续对偶：H(T) = log Z(T) + E(T)/T，∂H/∂T = Var_T(E)/T² ≥ 0。
     构造性离散版不走导数，走**代数恒等式**（本件件 2）：
       对任意两正温度 t1 t2（无需任何序前提）：
         ΔH := H(p_{t2}) − H(p_{t1})
            == β₂·(E₂ − E₁) + KL(p_{t1} ‖ p_{t2})      （β₂ := 1/t₂）
       三行证明：
         RHS = β₂E₂ − β₂E₁ + (−H₁ + β₂E₁ + log Z₂)   [KL 温度分解
                relative_entropy_temp_decomp（根 L17356）]
             = β₂E₂ + log Z₂ − H₁
             = H₂ − H₁                                 [熵显式
                entropy_temp_explicit（根 L17271）]
       KL 项承担了连续版 Var_T(E) 的角色——"离散方差"。
     单调（件 1）是恒等式的推论：
       t1 < t2 ⟹ E₁ ≤ E₂（根 energy_exp_temp_mono，L17521）
              ⟹ β₂·(E₂−E₁) ≥ 0（β₂ > 0，le_mult_compat_r）
       KL ≥ 0（根 gibbs_inequality，L16629）
       ⟹ ΔH ≥ 0 ⟹ H(p_{t1}) ≤ H(p_{t2})。
     对称 KL 恒等（根 temp_strict_ident2，L17879）：
       (β₁−β₂)·(E₂−E₁) == KL(p_{t2}‖p_{t1}) + KL(p_{t1}‖p_{t2})
     与件 2 联立消 ΔE 得第二恢复形态（件 2 alt）：
       ΔH == β₁·(E₂−E₁) − KL(p_{t2}‖p_{t1})
     （除法式 ΔH == β₂(K₁₂+K₂₁)/(β₁−β₂) + K₂₁ 需 inv_pos 链，
       无增量信息，诚实弃用。）

   交付件：
     件 1  entropy_temp_mono：t1 < t2 ⟹ H(p_{t1}) ≤ H(p_{t2})
           （严格前提版；接口层 le 序不可判定，非严格版以件 2
             恒等式为精确内容——恒等式对一切正温度对成立）
     件 2  recovery_entropy_gain：恢复增益精确恒等式（主形态）
           + recovery_entropy_gain_alt：对称 KL 联立形态
           + entropy_temp_strict_mono：严格单调档
            （诚实条件 T4.3 同款：KL(p_{t2}‖p_{t1}) > 0）
     件 3  fw_verdict（Or 编码健康/退化判定）+ fw_detect_warm
           （退化 ⟹ sigT 升温目标 t' := t+t 与恢复证书）
           + firewall_loop（闭环：温度不降 + 熵不降 + 判定重装）

   诚实边界（写进头的红线）：
     1) 熵防火墙不主张 TV-熵传递（Pinsker 型在册构造性红线）——
        闭环只证"升温 ⟹ 熵不降（且增量有精确分解）"，
        不证"熵恢复 ⟹ 分布距离收缩"。
     2) 闭环为证书形态非可判定检测：Real 层序不可判定（接口 le
        无三分律；root L139-141 已移除 le_lt_dec 并注明其经典性），
        fw_verdict 的 Or 是**证书和**（A+B），不是布尔判定器。
     3) 诚实接口假设（全部有根内同名先例，非经典公理）：
          base_loss / sum_over_S_pos / Z_temp / Z_temp_spec
            —— 根 FreeEnergyMinimization 区同名 Variable 复刻；
          inv_pos_lt_compat / lt_minus_nonneg
            —— 根 T2.2 区同名 Variable（L17119-17121）复刻，
               Real 层可实例化；
          lt_plus_compat_lt_le
            —— 根 ConvergenceCauchy 区同名 Variable 先例
               （UpEntropyGain.v 同名复用），仅用于升温目标
               t' := t+t 的严格性 lt t (t+t)。

   纪律：纯构造性 / Set 层 / 语句零 Prop（Id/le/lt/And:=A*B/
        Or:=A+b/sigT）/ 全程零未证缺口、零经典公理 / 可提取
        OCaml（提取产物经验收关卡核验）。
   ============================================================ *)

Section FirewallLoop.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

(* 解包接口字段（同根 FreeEnergyMinimization 区先例） *)
Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let le := @le RI.
Let lt := @lt RI.
Let log := @log RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.
(* minus 保持根全局 Definition（minus a b := plus a (opp b)） *)

Variable base_loss : S -> R.
Variable sum_over_S_pos : forall f : S -> R,
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).
Variable Z_temp : R -> R.
Variable Z_temp_spec : forall (t : R) (Ht : lt zero t),
  Id (Z_temp t) (sum_over_S (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).
(* 严格性接口（根 T2.2 区同名 Variable 复刻） *)
Variable inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Variable lt_minus_nonneg : forall a b : R, lt a b -> lt zero (minus b a).
(* 混合 lt+le 加法保序（根 ConvergenceCauchy 区同名 Variable 先例；
   仅用于升温目标 t' := t+t 的严格性） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* 温度参数化 Boltzmann 族速记（根 L17209/17212 全参显式） *)
Let Bt (t : R) (Ht : lt zero t) : S -> R :=
  boltzmann_dist_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.
Let Et (t : R) (Ht : lt zero t) : R :=
  energy_exp_temp base_loss sum_over_S_pos Z_temp Z_temp_spec t Ht.

(* ===== 基础引理 ===== *)

(* 能量期望的 η-形式桥：energy_expectation (Bt t) 定义性 == Et t *)
Lemma fw_energy_eta : forall (t : R) (Ht : lt zero t),
  Id (energy_expectation base_loss (Bt t Ht)) (Et t Ht).
Proof. intros t Ht. apply id_refl. Qed.

(* 倍温严格升：t > 0 ⟹ t < t + t（升温目标的构造性证书）
   （接口 plus 抽象：plus zero t 与 t 非转换可互换，
     须走 id_transport——抽象层 Id 假设禁 rewrite 的标准通路） *)
Lemma fw_lt_double : forall t : R, forall Ht : lt zero t,
  lt t (plus t t).
Proof.
  intros t Ht.
  apply (id_transport (fun w => lt w (plus t t))
                      (id_trans (plus_comm zero t) (plus_zero t))).
  apply (lt_plus_compat_lt_le zero t t t Ht (le_refl t)).
Qed.

(* 倍温正性：t > 0 ⟹ t + t > 0 *)
Lemma fw_double_pos : forall t : R, forall Ht : lt zero t,
  lt zero (plus t t).
Proof.
  intros t Ht. apply plus_positive; exact Ht.
Qed.

(* ===== 件 2（主交付）：恢复增益精确恒等式 =====
   ΔH := H(p_{t2}) − H(p_{t1}) == β₂·(E₂ − E₁) + KL(p_{t1} ‖ p_{t2})
   三行证明：KL 温度分解 + 熵显式 + 纯 AC 重排。 *)
Theorem recovery_entropy_gain : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
           (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
Proof.
  intros t1 t2 Ht1 Ht2.
  unfold minus.
  set (b2 := inv_pos t2 Ht2).
  set (E1 := Et t1 Ht1). set (E2 := Et t2 Ht2).
  set (H1 := entropy_dist (Bt t1 Ht1)). set (H2 := entropy_dist (Bt t2 Ht2)).
  set (K := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  set (L2 := log (Z_temp t2)).
  (* 熵显式：H2 == b2·E2 + L2 *)
  assert (Hex2 : Id H2 (plus (mult b2 E2) L2))
    by exact (entropy_temp_explicit base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
  (* KL 温度分解：K == (−H1 + b2·E1) + L2
     （energy_expectation (Bt t1) 定义性 == E1，fw_energy_eta 同 id_refl） *)
  assert (Hkl : Id K (plus (plus (opp H1) (mult b2 E1)) L2)).
  { apply (id_trans (relative_entropy_temp_decomp base_loss sum_over_S_pos Z_temp Z_temp_spec
                                  t2 Ht2 (Bt t1 Ht1)
                                  (boltzmann_dist_temp_normalized base_loss sum_over_S_pos
                                     Z_temp Z_temp_spec t1 Ht1))).
    apply (id_cong (fun x => plus (plus (opp H1) (mult b2 x)) L2)).
    apply fw_energy_eta. }
  (* 差的左分配：b2·(E2−E1) == b2·E2 + −(b2·E1) *)
  assert (Hd : Id (mult b2 (minus E2 E1)) (plus (mult b2 E2) (opp (mult b2 E1)))).
  { apply (id_trans (mult_minus_distr_l b2 E2 E1)).
    unfold minus. apply id_refl. }
  (* 主代数链（纯 AC）：
     b2(E2−E1) + ((−H1+b2E1)+L2) == (b2E2 + −(b2E1)) + ((−H1+b2E1)+L2)
       == b2E2 + ((−(b2E1)) + ((−H1+b2E1)+L2))
       == b2E2 + ((−(b2E1)) + (b2E1 + (−H1+L2)))
       == b2E2 + ((−(b2E1) + b2E1) + (−H1+L2))
       == b2E2 + (−H1+L2)
       == (b2E2 + L2) + −H1 == H2 + −H1 *)
  assert (Hrot : forall aX : R,
    Id (plus (plus (opp H1) aX) L2) (plus aX (plus (opp H1) L2))).
  { intros aX.
    apply (id_trans (id_sym (plus_assoc (opp H1) aX L2))).
    apply (id_trans (id_cong (fun w => plus (opp H1) w) (plus_comm aX L2))).
    apply (id_trans (plus_assoc (opp H1) L2 aX)).
    apply (plus_comm (plus (opp H1) L2) aX). }
  assert (Hchain : Id (plus (mult b2 (minus E2 E1)) (plus (plus (opp H1) (mult b2 E1)) L2))
                      (plus H2 (opp H1))).
  { apply (id_trans (id_cong (fun x => plus x (plus (plus (opp H1) (mult b2 E1)) L2)) Hd)).
    apply (id_trans (id_sym (plus_assoc (mult b2 E2) (opp (mult b2 E1))
                                        (plus (plus (opp H1) (mult b2 E1)) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus (opp (mult b2 E1)) w))
                             (Hrot (mult b2 E1)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_assoc (opp (mult b2 E1)) (mult b2 E1)
                                         (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) (plus w (plus (opp H1) L2)))
                             (id_trans (plus_comm (opp (mult b2 E1)) (mult b2 E1))
                                       (plus_opp (mult b2 E1))))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_comm zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w)
                             (plus_zero (plus (opp H1) L2)))).
    apply (id_trans (id_cong (fun w => plus (mult b2 E2) w) (plus_comm (opp H1) L2))).
    apply (id_trans (plus_assoc (mult b2 E2) L2 (opp H1))).
    apply (id_cong (fun w => plus w (opp H1)) (id_sym Hex2)). }
  apply (id_sym (id_trans (id_cong (fun x => plus (mult b2 (minus E2 E1)) x) Hkl) Hchain)).
Qed.

(* ===== 件 1（主交付）：温度-熵单调 =====
   t1 < t2 ⟹ H(p_{t1}) ≤ H(p_{t2})。
   路径：能量单调（根）+ 件 2 恒等式 + KL ≥ 0（根 Gibbs）。 *)
Theorem entropy_temp_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 -> le (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt.
  (* E1 ≤ E2（根 T2.2 主定理 energy_exp_temp_mono） *)
  assert (HdE : le zero (minus (Et t2 Ht2) (Et t1 Ht1))).
  { apply le_minus_nonneg.
    exact (energy_exp_temp_mono base_loss sum_over_S_pos inv_pos_lt_compat
             lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt). }
  (* KL(p_{t1} ‖ p_{t2}) ≥ 0（根 Gibbs 不等式） *)
  assert (Hkl : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  (* β₂ > 0 ⟹ β₂·ΔE ≥ 0 *)
  assert (Hb2 : le zero (inv_pos t2 Ht2)).
  { apply (lt_le_iff _ _). left. exact (inv_pos_pos t2 Ht2). }
  assert (Hterm : le zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
  { apply (le_id_l zero (mult (inv_pos t2 Ht2) zero)
                     (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))).
    - exact (id_sym (mult_zero (inv_pos t2 Ht2))).
    - exact (le_mult_compat_r (inv_pos t2 Ht2) zero (minus (Et t2 Ht2) (Et t1 Ht1)) Hb2 HdE). }
  (* 两非负项相加 ≥ 0 *)
  assert (Hsum : le zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                        (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                        Hterm
                        (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                          (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl)).
  (* 件 2 恒等式搬运：ΔH ≥ 0 *)
  assert (Hfin : le zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))).
  { apply (le_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                              (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))).
    - exact (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)).
    - exact Hsum. }
  (* H1 + ΔH == H2（minus_plus_cancel）⟹ H1 ≤ H2 *)
  apply (le_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - exact (le_plus_nonneg_r (entropy_dist (Bt t1 Ht1))
                            (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))) Hfin).
Qed.

(* ===== 件 2 严格档：升温 ⟹ 熵严格恢复 =====
   诚实条件（根 T4.3 同款）：KL(p_{t2} ‖ p_{t1}) > 0
   （分布非平凡时满足；KL 退化为零仅当两温度分布逐点相同）。
   路径：根 energy_exp_temp_strict_mono 给 ΔE > 0 ⟹ β₂ΔE > 0，
   加 KL ≥ 0 后由件 2 恒等式搬运。 *)
Theorem entropy_temp_strict_mono : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  lt t1 t2 ->
  lt zero (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)) ->
  lt (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl12.
  assert (HdE : lt zero (minus (Et t2 Ht2) (Et t1 Ht1)))
    by exact (energy_exp_temp_strict_mono base_loss sum_over_S_pos inv_pos_lt_compat
                lt_minus_nonneg Z_temp Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl12).
  assert (Hterm : lt zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))))
    by exact (mult_positive (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1))
                            (inv_pos_pos t2 Ht2) HdE).
  assert (Hkl21 : le zero (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))).
  { apply (gibbs_inequality (Bt t1 Ht1) (Bt t2 Ht2)).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t1 Ht1 s).
    - exact (boltzmann_dist_temp_normalized base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2).
    - intros s. exact (boltzmann_dist_temp_pos base_loss sum_over_S_pos Z_temp Z_temp_spec t2 Ht2 s). }
  assert (Hsum : lt zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                               (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2))))
    by exact (lt_le_trans zero (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                          (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                          Hterm
                          (le_plus_nonneg_r (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                            (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)) Hkl21)).
  assert (Hfin : lt zero (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
    by exact (lt_id_r zero (plus (mult (inv_pos t2 Ht2) (minus (Et t2 Ht2) (Et t1 Ht1)))
                                  (relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                       (id_sym (recovery_entropy_gain t1 t2 Ht1 Ht2)) Hsum).
  apply (lt_id_r (entropy_dist (Bt t1 Ht1))
                 (plus (entropy_dist (Bt t1 Ht1))
                       (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1))))
                 (entropy_dist (Bt t2 Ht2))).
  - exact (minus_plus_cancel (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t2 Ht2))).
  - (* lt H1 (H1 + ΔH)：两侧各走一次 id_transport
       （zero + H1 ↦ H1；ΔH + H1 ↦ H1 + ΔH；接口 plus 抽象不可换形） *)
    apply (id_transport
             (fun w => lt w (plus (entropy_dist (Bt t1 Ht1))
                                  (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))))
             (id_trans (plus_comm zero (entropy_dist (Bt t1 Ht1)))
                       (plus_zero (entropy_dist (Bt t1 Ht1))))).
    apply (id_transport
             (fun w => lt (plus zero (entropy_dist (Bt t1 Ht1))) w)
             (plus_comm (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                        (entropy_dist (Bt t1 Ht1)))).
    exact (lt_plus_compat_lt_le zero
                                (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
                                (entropy_dist (Bt t1 Ht1)) (entropy_dist (Bt t1 Ht1))
                                Hfin (le_refl (entropy_dist (Bt t1 Ht1)))).
Qed.

(* ===== 件 2 对偶形态：对称 KL 联立 =====
   与根 temp_strict_ident2（(β₁−β₂)ΔE == K12 + K21）联立消 (β₁−β₂)ΔE：
   ΔH == β₁·ΔE − K12（K12 := KL(p_{t2} ‖ p_{t1})）。
   三个恢复量（ΔH, ΔE, KL 组合）的完整系数表到此闭合。 *)
Theorem recovery_entropy_gain_alt : forall t1 t2 : R, forall Ht1 : lt zero t1, forall Ht2 : lt zero t2,
  Id (minus (entropy_dist (Bt t2 Ht2)) (entropy_dist (Bt t1 Ht1)))
     (minus (mult (inv_pos t1 Ht1) (minus (Et t2 Ht2) (Et t1 Ht1)))
            (relative_entropy (Bt t2 Ht2) (Bt t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  set (b1 := inv_pos t1 Ht1). set (b2 := inv_pos t2 Ht2).
  set (dE := minus (Et t2 Ht2) (Et t1 Ht1)).
  set (K12 := relative_entropy (Bt t2 Ht2) (Bt t1 Ht1)).
  set (K21 := relative_entropy (Bt t1 Ht1) (Bt t2 Ht2)).
  (* 对称 KL 恒等（根 temp_strict_ident2） *)
  assert (Hsym : Id (plus K12 K21) (mult (minus b1 b2) dE))
    by exact (temp_strict_ident2 base_loss sum_over_S_pos Z_temp Z_temp_spec t1 t2 Ht1 Ht2).
  (* b1 == b2 + (b1 − b2) *)
  assert (Hb1 : Id b1 (plus b2 (minus b1 b2))).
  { apply id_sym.
    apply (id_trans (plus_assoc b2 b1 (opp b2))).
    apply (id_trans (id_cong (fun w => plus w (opp b2)) (plus_comm b2 b1))).
    apply (id_trans (id_sym (plus_assoc b1 b2 (opp b2)))).
    apply (id_trans (id_cong (fun w => plus b1 w) (plus_opp b2))).
    apply (plus_zero b1). }
  (* 分配：b1·ΔE == b2·ΔE + (b1−b2)·ΔE *)
  assert (Hdistr : Id (mult b1 dE) (plus (mult b2 dE) (mult (minus b1 b2) dE))).
  { apply (id_trans (id_cong (fun w => mult w dE) Hb1)).
    apply (mult_plus_distr_r b2 (minus b1 b2) dE). }
  (* (b1−b2)·ΔE == K21 + K12（Hsym 对换） *)
  assert (Hsym' : Id (mult (minus b1 b2) dE) (plus K21 K12))
    by exact (id_trans (id_sym Hsym) (plus_comm K12 K21)).
  (* 减法消去：(K21 + K12) − K12 == K21 *)
  assert (Hcancel : Id (minus (plus K21 K12) K12) K21).
  { unfold minus.
    apply (id_trans (id_sym (plus_assoc K21 K12 (opp K12)))).
    apply (id_trans (id_cong (fun w => plus K21 w) (plus_opp K12))).
    apply (plus_zero K21). }
  (* 组装：ΔH == b2ΔE + K21（件 2）
       == (b2ΔE + (K21+K12)) − K12 == (b2ΔE + (b1−b2)ΔE) − K12 == b1ΔE − K12 *)
  assert (Hstep1 : Id (plus (mult b2 dE) K21)
                      (minus (plus (mult b2 dE) (plus K21 K12)) K12)).
  { apply (id_trans (id_cong (fun w => plus (mult b2 dE) w) (id_sym Hcancel))).
    apply (plus_assoc (mult b2 dE) (plus K21 K12) (opp K12)). }
  assert (Hstep2 : Id (minus (plus (mult b2 dE) (plus K21 K12)) K12)
                      (minus (mult b1 dE) K12)).
  { apply (id_cong (fun w => minus w K12)
                   (id_sym (id_trans Hdistr
                     (id_cong (fun w => plus (mult b2 dE) w) Hsym')))). }
  apply (id_trans (recovery_entropy_gain t1 t2 Ht1 Ht2)).
  exact (id_trans Hstep1 Hstep2).
Qed.

(* ===== 件 3：闭环封装（证书形态状态机） =====

   fw_verdict：健康判定 = Or 证书和（Set 层，非布尔判定器）
     - inl：健康证书 —— 熵过阈值 H_min 的 le 证书；
     - inr：退化报告 —— 量化缺口的 sigT 单元素类型（gap 恒等于
       当前熵 − H_min 的差值，携带"还差多少"的可提取实数）。
       （注意层级：Or 的分支是类型不是项——实数本身不能作分支，
         须经 sigT 单元素类型承载。）
   firewall_loop：闭环转移 —— 任一判定 ⟹ sigT 见证后继温度
     （健康：驻留 t' := t；退化：倍温 t' := t + t），
     携带转移证书（温度不降 + 熵不降 + 判定重装）。
   诚实边界：单轮迭代不宣称"恢复健康"——退化支的重装判定
     仍是 inr（新一轮缺口报告）；健康与否由下一轮 fw_verdict
     证书回答。循环不变量 = 温度不降 ∧ 熵不降（件 1/2 供给）。 *)

Definition fw_verdict (Hmin : R) (t : R) (Ht : lt zero t) : Set :=
  Or (le Hmin (entropy_dist (Bt t Ht)))
     (sigT (fun gap : R => Id gap (minus (entropy_dist (Bt t Ht)) Hmin))).

(* 检测-升温响应：退化报告 ⟹ sigT 见证升温目标 t' := t + t
   与恢复证书（熵不降 + 增量精确分解 = 件 2 恒等式） *)
Theorem fw_detect_warm : forall (Hmin : R) (t : R) (Ht : lt zero t)
                                (Hdef : sigT (fun gap : R =>
                                          Id gap (minus (entropy_dist (Bt t Ht)) Hmin))),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (lt t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (Id (minus (entropy_dist (Bt t' Ht')) (entropy_dist (Bt t Ht)))
                 (plus (mult (inv_pos t' Ht') (minus (Et t' Ht') (Et t Ht)))
                       (relative_entropy (Bt t Ht) (Bt t' Ht'))))))).
Proof.
  intros Hmin t Ht Hdef.
  assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
  assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
  exists (plus t t). exists Ht'.
  split.
  - exact Hup.
  - split.
    + exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
    + exact (recovery_entropy_gain t (plus t t) Ht Ht').
Qed.

(* 闭环主定理：任一判定 ⟹ sigT 后继状态
   （温度不降 ∧ 熵不降 ∧ 判定重装）——逐轮可重复应用的
   证书状态机转移；健康支驻留、退化支倍温。 *)
Theorem firewall_loop : forall (Hmin : R) (t : R) (Ht : lt zero t)
                              (v : fw_verdict Hmin t Ht),
  sigT (fun t' => sigT (fun Ht' : lt zero t' =>
    And (le t t')
        (And (le (entropy_dist (Bt t Ht)) (entropy_dist (Bt t' Ht')))
             (fw_verdict Hmin t' Ht')))).
Proof.
  intros Hmin t Ht v. destruct v as [Hok | Hdef].
  - (* 健康支：驻留 *)
    exists t. exists Ht.
    split.
    + apply le_refl.
    + split.
      * apply le_refl.
      * left. exact Hok.
  - (* 退化支：倍温 t' := t + t，熵恢复（件 1），判定重装（诚实：仍 inr） *)
    assert (Ht' : lt zero (plus t t)) by exact (fw_double_pos t Ht).
    assert (Hup : lt t (plus t t)) by exact (fw_lt_double t Ht).
    exists (plus t t). exists Ht'.
    split.
    + apply (lt_le_iff _ _). left. exact Hup.
    + split.
      * exact (entropy_temp_mono t (plus t t) Ht Ht' Hup).
      * right. exact (existT _ (minus (entropy_dist (Bt (plus t t) Ht')) Hmin) id_refl).
Qed.

End FirewallLoop.

(* ============ 提取探针（可执行 OCaml，验收关卡） ============ *)
Set Warnings "-extraction-opaque-accessed".

Extraction "upfirewall.ml" entropy_temp_mono recovery_entropy_gain recovery_entropy_gain_alt entropy_temp_strict_mono fw_detect_warm firewall_loop.

(* ---------- UpTempWindow ---------- *)
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax QArith.QOrderedType.
(* ============================================================ *)
(* UpTempWindow.v —— 温度窗口 T→∞ 半边：有界 logits softmax 核   *)
(*   高温趋近均匀分布（量词翻转的真极限定理，sigT 见证）。       *)
(*                                                              *)
(*   主定理 temp_window_T_infty：                                *)
(*     ∀eps > 0, ∃T₂ > 0, ∀T > T₂, TV(w_T, U) ≤ eps             *)
(*                                                              *)
(*   设定：list 离散状态世界（镜像 AttnHardLimit）：             *)
(*     states : list S 非空；logits z : S -> Real 一致界         *)
(*     |z(s)| ≤ Δ（Δ > 0）；w_T(x) = e^{z(x)/T}/Z(T)；           *)
(*     uniform(x) = 1/N（N = |states|）；TV = Σ|w_T − 1/N|。     *)
(*                                                              *)
(*   核心不等式（Doeblin 均匀版）：                              *)
(*     e^{−2Δ/T}/N ≤ w_T(x) ≤ e^{+2Δ/T}/N                       *)
(*   ⟹ 逐点 |w_T(x) − 1/N| ≤ (e^{2Δ/T} − 1)/N                   *)
(*   ⟹ TV ≤ e^{2Δ/T} − 1。                                      *)
(*   量词翻转：T₂ := 2Δ/cw_log(1+eps) + 1，                     *)
(*     T > T₂ ⟹ 2Δ/T ≤ cw_log(1+eps) ⟹ e^{2Δ/T} ≤ 1+eps。      *)
(*                                                              *)
(*   纪律：纯构造性、零 Axiom/Admitted/Abort/Classical；         *)
(*         语句全 Set 层（sigT/And/Or）；全部 Qed。              *)
(* ============================================================ *)


(* ============================================================ *)
(* 0. 通用桥（Real 层，Section 外，全局可复用）                 *)
(* ============================================================ *)

(* lt ⟹ le（real_le 的 Or 编码左支） *)
Lemma tw_lt_le : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H. exact (inl H).
Qed.

(* eq ⟹ le（Or 编码右支） *)
Lemma tw_eq_le : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  intros a b H. exact (inr H).
Qed.

(* a ≤ b 且 b == c ⟹ a ≤ c *)
Lemma tw_le_eq_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hab Hbc. exact (real_le_trans a b c Hab (inr Hbc)).
Qed.

(* a ≤ b 且 a == c ⟹ c ≤ b *)
Lemma tw_le_eq_l : forall a b c : Real,
  real_le a b -> real_eq a c -> real_le c b.
Proof.
  intros a b c Hab Hac.
  exact (real_le_trans c a b (inr (real_eq_sym a c Hac)) Hab).
Qed.

(* 0 ≤ b ⟹ a ≤ a + b *)
Lemma tw_le_plus_nonneg_r : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat; [apply real_le_refl | exact Hb].
Qed.

(* 0 < y ⟹ −y < 0（见证不变，逐点 0−(−y_k) == y_k） *)
Lemma tw_lt_opp_l : forall y : Real,
  real_lt real_zero y -> real_lt (real_opp y) real_zero.
Proof.
  intros y H. destruct H as [e [He [N HN]]].
  destruct y as [u Hu].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    cbn [projT1 real_opp real_zero].
    assert (Hy : Qlt e (u n - 0)) by (apply QltT_to_Qlt; exact (HN n Hn)).
    assert (Hz : u n - 0 == u n) by ring.
    rewrite Hz in Hy.
    apply Qlt_to_QltT.
    assert (Hz2 : 0 - - u n == u n) by ring.
    rewrite Hz2.
    exact Hy.
Qed.

(* ============================================================ *)
(* 1. 纯环原子恒等式族（real_eq_of_zero_diff 逐点 ring，N = 0） *)
(*   惯例：原子以 Real 变量抽象，destruct 后 simpl 全消 projT1。 *)
(* ============================================================ *)

(* 0 + x == x（zero 在左） *)
Lemma tw_ring_zero_plus : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (d+d)·e == d·e + d·e *)
Lemma tw_ring_dd_mult : forall d e : Real,
  real_eq (real_mult (real_plus d d) e)
          (real_plus (real_mult d e) (real_mult d e)).
Proof.
  intros d e. destruct d as [u Hu]. destruct e as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x+y)·z == x·z + y·z（右分配） *)
Lemma tw_ring_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z)
          (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x·y + (−y) == (x + (−1))·y *)
Lemma tw_ring_sub_mult : forall x y : Real,
  real_eq (real_plus (real_mult x y) (real_opp y))
          (real_mult (real_plus x (real_opp real_one)) y).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* y + −(x·y) == (1 + −x)·y *)
Lemma tw_ring_sub_mult_l : forall x y : Real,
  real_eq (real_plus y (real_opp (real_mult x y)))
          (real_mult (real_plus real_one (real_opp x)) y).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (1+e) + (−1) == e *)
Lemma tw_ring_one_eps_minus : forall e : Real,
  real_eq (real_plus (real_plus real_one e) (real_opp real_one)) e.
Proof.
  intros e. destruct e as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* T₂·L == 2Δ·(L·invL) + L，其中 T₂ = 2Δ·invL + 1（翻转链换形） *)
Lemma tw_ring_t2 : forall d l il : Real,
  real_eq (real_mult l (real_plus (real_mult (real_plus d d) il) real_one))
          (real_plus (real_mult (real_plus d d) (real_mult l il)) l).
Proof.
  intros d l il. destruct d as [u Hu]. destruct l as [v Hv]. destruct il as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (2Δ + L)·invT == 2Δ·invT + L·invT *)
Lemma tw_ring_ddl : forall d l it : Real,
  real_eq (real_mult (real_plus (real_plus d d) l) it)
          (real_plus (real_mult (real_plus d d) it) (real_mult l it)).
Proof.
  intros d l it. destruct d as [u Hu]. destruct l as [v Hv]. destruct it as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* u + −(2u) == −u（u = Δ/T，2u = EF） *)
Lemma tw_ring_u_plus_negEF : forall d it : Real,
  real_eq (real_plus (real_mult d it)
                     (real_opp (real_mult (real_plus d d) it)))
          (real_opp (real_mult d it)).
Proof.
  intros d it. destruct d as [u Hu]. destruct it as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −u + 2u == u *)
Lemma tw_ring_negu_plus_EF : forall d it : Real,
  real_eq (real_plus (real_opp (real_mult d it))
                     (real_mult (real_plus d d) it))
          (real_mult d it).
Proof.
  intros d it. destruct d as [u Hu]. destruct it as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x == (x+x) + (−x)（x+x ~ 0 时归零链用） *)
Lemma tw_ring_self_minus : forall x : Real,
  real_eq x (real_plus (real_plus x x) (real_opp x)).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x+x) 换形：x + x == 2·x 的右分配形态（配 inv_pos_correct(1+1) 用） *)
Lemma tw_ring_two_split : forall x h : Real,
  real_eq (real_plus (real_mult x h) (real_mult x h))
          (real_mult x (real_mult (real_plus real_one real_one) h)).
Proof.
  intros x h. destruct x as [u Hu]. destruct h as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x + −(−x) == x + x *)
Lemma tw_ring_xopp_x : forall x : Real,
  real_eq (real_plus x (real_opp (real_opp x))) (real_plus x x).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −x·h == −(x·h) *)
Lemma tw_ring_opp_mult : forall x h : Real,
  real_eq (real_mult (real_opp x) h) (real_opp (real_mult x h)).
Proof.
  intros x h. destruct x as [u Hu]. destruct h as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −x + x == 0 *)
Lemma tw_ring_opp_plus : forall x : Real,
  real_eq (real_plus (real_opp x) x) real_zero.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* ============================================================ *)
(* 2. Q 层助手：QltT 的构造/传输与 Qmin 事实                    *)
(*    QltT x y == Id (Qlt_bool x y) true（非集合体，不可 setoid）*)
(*    ⟹ 一律经 Qcompare = Lt 通道构造，再 Qeq 传输。            *)
(* ============================================================ *)

(* Qcompare = Lt ⟹ QltT（unfold 后改写 match 判别式） *)
Lemma tw_QltT_from_Qcompare : forall a b : Q, Qcompare a b = Lt -> QltT a b.
Proof.
  intros a b H. unfold QltT, Qlt_bool. rewrite H. reflexivity.
Qed.

(* QltT a b 且 b == c ⟹ QltT a c *)
Lemma tw_QltT_transport : forall a b c : Q,
  QltT a b -> b == c -> QltT a c.
Proof.
  intros a b c Hab Hbc.
  apply tw_QltT_from_Qcompare.
  assert (Hcmp : Qcompare a b = Lt).
  { apply Qlt_alt. apply QltT_to_Qlt. exact Hab. }
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b c Hbc).
  exact Hcmp.
Qed.

(* Qmin 事实（GenericMinMax 经 Qminmax.Q 实例化） *)
Lemma tw_Q_min_l : forall e1 e2 : Q, e1 <= e2 -> Qmin e1 e2 == e1.
Proof.
  intros e1 e2 H. apply Q.min_l. exact H.
Qed.

Lemma tw_Q_min_r : forall e1 e2 : Q, e2 <= e1 -> Qmin e1 e2 == e2.
Proof.
  intros e1 e2 H. apply Q.min_r. exact H.
Qed.

Lemma tw_Q_le_min_l : forall e1 e2 : Q, Qle (Qmin e1 e2) e1.
Proof.
  intros e1 e2.
  destruct (Qlt_le_dec e1 e2) as [H | H].
  - rewrite (tw_Q_min_l e1 e2 (Qlt_le_weak _ _ H)).
    apply Qle_refl.
  - rewrite (tw_Q_min_r e1 e2 H).
    exact H.
Qed.

Lemma tw_Q_le_min_r : forall e1 e2 : Q, Qle (Qmin e1 e2) e2.
Proof.
  intros e1 e2.
  destruct (Qlt_le_dec e1 e2) as [H | H].
  - rewrite (tw_Q_min_l e1 e2 (Qlt_le_weak _ _ H)).
    apply Qlt_le_weak. exact H.
  - rewrite (tw_Q_min_r e1 e2 H).
    apply Qle_refl.
Qed.

(* 正的 Qmin：两见证皆正 ⟹ min 正 *)
Lemma tw_Q_pos_min : forall e1 e2 : Q,
  QltT 0 e1 -> QltT 0 e2 -> QltT 0 (Qmin e1 e2).
Proof.
  intros e1 e2 He1 He2.
  apply tw_QltT_from_Qcompare.
  destruct (Qlt_le_dec e1 e2) as [H | H].
  - rewrite (tw_Q_min_l e1 e2 (Qlt_le_weak _ _ H)).
    apply Qlt_alt. apply QltT_to_Qlt. exact He1.
  - rewrite (tw_Q_min_r e1 e2 H).
    apply Qlt_alt. apply QltT_to_Qlt. exact He2.
Qed.

(* 折半：0 < e < 2y 形态 ⟹ e/2 < y（Q 层，经 field + Qlt_irrefl） *)
Lemma tw_Q_half_lt : forall e y : Q, QltT e (y + y) -> QltT (e / 2) y.
Proof.
  intros e y H.
  assert (Hcmp : Qcompare (e / 2) y = Lt).
  { destruct (Qlt_le_dec (e / 2) y) as [Hyes | Hno].
    - apply Qlt_alt. exact Hyes.
    - exfalso.
      assert (H2 : y + y <= e / 2 + e / 2)
        by (apply Qplus_le_compat; exact Hno).
      assert (H3 : e / 2 + e / 2 == e) by field.
      rewrite H3 in H2.
      assert (H4 : Qlt e e) by (apply (Qlt_le_trans e (y + y) e);
                               [apply QltT_to_Qlt; exact H | exact H2]).
      exact (Qlt_irrefl e H4). }
  apply tw_QltT_from_Qcompare. exact Hcmp.
Qed.

(* ============================================================ *)
(* 3. Real 层见证折半与 exp 恒等式                              *)
(* 0 < y + y ⟹ 0 < y *)
Lemma tw_lt_half : forall y : Real,
  real_lt real_zero (real_plus y y) -> real_lt real_zero y.
Proof.
  intros y H. destruct H as [e [He [N HN]]].
  destruct y as [u Hu].
  exists (e / 2)%Q. split.
  - (* 0 < e/2：反证 e/2 ≤ 0 ⟹ e ≤ 0 与 He 矛盾 *)
    destruct (Qlt_le_dec 0 (e / 2)) as [Hyes | Hno].
    + apply Qlt_to_QltT. exact Hyes.
    + exfalso.
      assert (H2 : e / 2 + e / 2 <= 0 + 0)
        by (apply Qplus_le_compat; exact Hno).
      assert (H3 : e / 2 + e / 2 == e) by field.
      assert (H4 : Qle e 0).
      { apply (Qle_trans e (e / 2 + e / 2) 0).
        - apply qeq_le. apply Qeq_sym. exact H3.
        - apply (Qle_trans (e / 2 + e / 2) (0 + 0) 0).
          + exact H2.
          + apply qeq_le. ring. }
      exact (Qlt_irrefl 0 (Qlt_le_trans 0 e 0 (QltT_to_Qlt 0 e He) H4)).
  - exists N. intros n Hn.
    cbn [projT1 real_plus real_zero].
    cbn [projT1 real_plus real_zero] in HN.
    apply tw_QltT_transport with (b := u n).
    + apply tw_Q_half_lt.
      apply (tw_QltT_transport e (u n + u n - 0) (u n + u n)).
      * exact (HN n Hn).
      * ring.
    + ring.
Qed.

(* 0 < y + y ⟹ −y < 0 *)
Lemma tw_lt_half_opp : forall y : Real,
  real_lt real_zero (real_plus y y) -> real_lt (real_opp y) real_zero.
Proof.
  intros y H. apply tw_lt_opp_l. apply tw_lt_half. exact H.
Qed.

(* exp 单调的 le 版（real_le 的 Or 编码分解到 mono/wd） *)
Lemma tw_exp_mono_le : forall a b : Real,
  real_le a b -> real_le (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (cauchy_real_exp_mono a b Hlt)).
  - exact (inr (cauchy_real_exp_wd a b Heq)).
Qed.

(* e^{−E}·e^{E} == 1（exp_plus + wd + exp_zero 链） *)
Lemma tw_exp_opp_prod : forall E : Real,
  real_eq (real_mult (cauchy_real_exp (real_opp E)) (cauchy_real_exp E))
          real_one.
Proof.
  intros E.
  apply (real_eq_trans _
           (cauchy_real_exp (real_plus (real_opp E) E)) _).
  - apply real_eq_sym. apply (cauchy_real_exp_plus (real_opp E) E).
  - apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
    + apply cauchy_real_exp_wd. apply tw_ring_opp_plus.
    + apply cauchy_real_exp_zero.
Qed.

(* 0 + o1 == o1 *)
Lemma tw_ring_zero_plus_one : forall o1 : Real,
  real_eq (real_plus real_zero o1) o1.
Proof.
  intros o1. destruct o1 as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x + −1) + 1 == x *)
Lemma tw_ring_add_one_back : forall x : Real,
  real_eq (real_plus (real_plus x (real_opp real_one)) real_one) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 1·x == x *)
Lemma tw_ring_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −x == −(1·x) *)
Lemma tw_eq_opp_mult_one : forall x : Real,
  real_eq (real_opp x) (real_opp (real_mult real_one x)).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x·(−1) == −x *)
Lemma tw_ring_mult_opp_one : forall x : Real,
  real_eq (real_mult x (real_opp real_one)) (real_opp x).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < E ⟹ 1 ≤ e^{E}（经 cauchy_real_exp_minus_one_pos） *)
Lemma tw_le_expE_one : forall E : Real,
  real_lt real_zero E -> real_le real_one (cauchy_real_exp E).
Proof.
  intros E HE.
  assert (Hm : real_lt real_zero
                 (real_plus (cauchy_real_exp E) (real_opp real_one)))
    by (apply (cauchy_real_exp_minus_one_pos E); exact HE).
  assert (Hle0 : real_le real_zero
                   (real_plus (cauchy_real_exp E) (real_opp real_one)))
    by (exact (inl Hm)).
  apply (tw_le_eq_l (real_plus real_zero real_one)
           (cauchy_real_exp E) real_one).
  - apply (tw_le_eq_r
             (real_plus real_zero real_one)
             (real_plus (real_plus (cauchy_real_exp E) (real_opp real_one))
                        real_one)
             (cauchy_real_exp E)).
    + apply real_le_plus_compat; [exact Hle0 | apply real_le_refl].
    + apply (tw_ring_add_one_back (cauchy_real_exp E)).
  - apply tw_ring_zero_plus_one.
Qed.

(* 0 < E ⟹ e^{−E} ≤ 1（右乘 e^{−E} > 0 保序 + 乘积恒等） *)
Lemma tw_le_exp_oppE_one : forall E : Real,
  real_lt real_zero E ->
  real_le (cauchy_real_exp (real_opp E)) real_one.
Proof.
  intros E HE.
  assert (Hc : real_lt real_zero (cauchy_real_exp (real_opp E)))
    by apply cauchy_real_exp_pos.
  assert (H1 : real_le real_one (cauchy_real_exp E))
    by (apply tw_le_expE_one; exact HE).
  assert (H2 : real_le (real_mult real_one (cauchy_real_exp (real_opp E)))
                       (real_mult (cauchy_real_exp E)
                                   (cauchy_real_exp (real_opp E))))
    by (apply (real_le_mult_compat real_one (cauchy_real_exp E) (cauchy_real_exp (real_opp E)) Hc H1)).
  apply (tw_le_eq_r (cauchy_real_exp (real_opp E))
           (real_mult (cauchy_real_exp E) (cauchy_real_exp (real_opp E)))
           real_one).
  - apply (tw_le_eq_l (real_mult real_one (cauchy_real_exp (real_opp E)))
             (real_mult (cauchy_real_exp E) (cauchy_real_exp (real_opp E)))
             (cauchy_real_exp (real_opp E))).
    + exact H2.
    + apply tw_ring_mult_one_l.
  - apply (real_eq_trans _
             (real_mult (cauchy_real_exp (real_opp E)) (cauchy_real_exp E)) _).
    + apply real_mult_comm.
    + apply tw_exp_opp_prod.
Qed.

(* 0 < E ⟹ 1 + −e^{−E} ≤ e^{E} + −1 *)
Lemma tw_one_minus_exp_le : forall E : Real,
  real_lt real_zero E ->
  real_le (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))
          (real_plus (cauchy_real_exp E) (real_opp real_one)).
Proof.
  intros E HE.
  assert (Hprod : real_eq (real_mult (cauchy_real_exp (real_opp E))
                                     (cauchy_real_exp E))
                          real_one) by exact (tw_exp_opp_prod E).
  assert (Halt : real_lt real_zero
                   (real_plus (cauchy_real_exp E) (real_opp real_one)))
    by exact (cauchy_real_exp_minus_one_pos E HE).
  (* a := e^{−E} < 1（tw_lt_opp_l + exp 单调 + exp_zero + eq 传输） *)
  assert (Ha1 : real_lt (cauchy_real_exp (real_opp E)) real_one).
  { apply (real_lt_eq_lt (cauchy_real_exp (real_opp E))
             (cauchy_real_exp real_zero) real_one).
    - apply (cauchy_real_exp_mono (real_opp E) real_zero).
      apply tw_lt_opp_l. exact HE.
    - apply cauchy_real_exp_zero. }
  assert (Hc1 : real_lt real_zero
                  (real_plus real_one (real_opp (cauchy_real_exp (real_opp E)))))
    by exact (real_lt_opp_plus (cauchy_real_exp (real_opp E)) real_one Ha1).
  assert (Hage : real_le real_one (cauchy_real_exp E))
    by exact (tw_le_expE_one E HE).
  assert (H2 : real_le (real_mult real_one
                                  (real_plus real_one
                                             (real_opp (cauchy_real_exp (real_opp E)))))
                       (real_mult (cauchy_real_exp E)
                                  (real_plus real_one
                                             (real_opp (cauchy_real_exp (real_opp E))))))
    by exact (real_le_mult_compat real_one (cauchy_real_exp E)
                (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))
                Hc1 Hage).
  (* b·(1−a) == b + −1：分配右 + 1·b ~ b + −(a·b) ~ b + −1 *)
  assert (E2 : real_eq (real_mult (cauchy_real_exp E)
                                  (real_plus real_one
                                             (real_opp (cauchy_real_exp (real_opp E)))))
                       (real_plus (cauchy_real_exp E) (real_opp real_one))).
  { apply (real_eq_trans _
             (real_plus (real_mult real_one (cauchy_real_exp E))
                        (real_mult (real_opp (cauchy_real_exp (real_opp E)))
                                   (cauchy_real_exp E))) _).
    - apply (real_eq_trans _
               (real_mult (real_plus real_one
                                     (real_opp (cauchy_real_exp (real_opp E))))
                          (cauchy_real_exp E)) _).
      + exact (real_mult_comm (cauchy_real_exp E)
                  (real_plus real_one
                             (real_opp (cauchy_real_exp (real_opp E))))).
      + exact (tw_ring_distrib_r real_one
                  (real_opp (cauchy_real_exp (real_opp E)))
                  (cauchy_real_exp E)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult real_one (cauchy_real_exp E))
               (real_mult (real_opp (cauchy_real_exp (real_opp E)))
                          (cauchy_real_exp E))
               (cauchy_real_exp E) (real_opp real_one)).
      + exact (tw_ring_mult_one_l (cauchy_real_exp E)).
      + apply (real_eq_trans _
                 (real_opp (real_mult (cauchy_real_exp (real_opp E))
                                      (cauchy_real_exp E))) _).
        * exact (tw_ring_opp_mult (cauchy_real_exp (real_opp E))
                    (cauchy_real_exp E)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (cauchy_real_exp (real_opp E))
                              (cauchy_real_exp E)) real_one).
          exact Hprod. }
  apply (tw_le_eq_r (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))
           (real_mult (cauchy_real_exp E)
                      (real_plus real_one
                                 (real_opp (cauchy_real_exp (real_opp E)))))
           (real_plus (cauchy_real_exp E) (real_opp real_one))).
  - apply (tw_le_eq_l (real_mult real_one
                              (real_plus real_one
                                         (real_opp (cauchy_real_exp (real_opp E)))))
             (real_mult (cauchy_real_exp E)
                        (real_plus real_one
                                   (real_opp (cauchy_real_exp (real_opp E)))))
             (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))).
    + exact H2.
    + exact (tw_ring_mult_one_l
               (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))).
  - exact E2.
Qed.
(* ============================================================ *)
(* 4. 双侧绝对值引理：|x| ≤ c ⟸ x ≤ c ∧ −x ≤ c                  *)
(*   四情形（lt/lt；eq/eq；lt/eq；eq/lt），eq 混合支用            *)
(*   real_abs_neg_req / real_abs_nonneg_req 符号归零。           *)
(* ============================================================ *)

Lemma tw_abs_le : forall x c : Real,
  real_le x c -> real_le (real_opp x) c -> real_le (real_abs x) c.
Proof.
  intros x c H1 H2.
  destruct H1 as [Hlt1 | Heq1]; destruct H2 as [Hlt2 | Heq2].
  - (* 双严格：见证 Qmin e1 e2；逐点按 u n 符号取分支 *)
    left.
    destruct Hlt1 as [e1 [He1 [N1 HN1]]].
    destruct Hlt2 as [e2 [He2 [N2 HN2]]].
    exists (Qmin e1 e2). split.
    + apply tw_Q_pos_min; assumption.
    + exists (Nat.max N1 N2). intros n Hn.
      destruct x as [u Hu]. destruct c as [v Hv].
      cbn [projT1 real_opp real_zero real_abs].
      assert (Hn1 : NatLe N1 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      assert (Hn2 : NatLe N2 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      assert (Ha : Qlt e1 (v n - u n)) by (apply QltT_to_Qlt; exact (HN1 n Hn1)).
      assert (Hb : Qlt e2 (v n - - u n)) by (apply QltT_to_Qlt; exact (HN2 n Hn2)).
      destruct (Qlt_le_dec (u n) 0) as [Hneg | Hpos].
      * assert (Habs : Qabs (u n) == - u n)
          by (apply Qabs_neg; apply Qlt_le_weak; exact Hneg).
        apply Qlt_to_QltT.
        apply (Qle_lt_trans (Qmin e1 e2) e2 (v n - Qabs (u n))).
        -- apply tw_Q_le_min_r.
        -- assert (Hq : v n - Qabs (u n) == v n - - u n).
           { rewrite Habs. reflexivity. }
           rewrite Hq. exact Hb.
      * assert (Habs : Qabs (u n) == u n) by (apply Qabs_pos; exact Hpos).
        apply Qlt_to_QltT.
        apply (Qle_lt_trans (Qmin e1 e2) e1 (v n - Qabs (u n))).
        -- apply tw_Q_le_min_l.
        -- assert (Hq : v n - Qabs (u n) == v n - u n).
           { rewrite Habs. reflexivity. }
           rewrite Hq. exact Ha.
  - (* x < c ∧ −x == c ⟹ x < −x ⟹ x < 0 ⟹ |x| == −x == c *)
    assert (Hxox : real_lt x (real_opp x)).
    { exact (real_lt_eq_lt x c (real_opp x) Hlt1
               (real_eq_sym (real_opp x) c Heq2)). }
    assert (Hx0 : real_lt x real_zero).
    { apply (real_eq_lt_lt x (real_opp (real_opp x)) real_zero).
      + apply real_eq_sym. apply real_opp_opp.
      + apply tw_lt_half_opp. exact (real_lt_opp_plus x (real_opp x) Hxox). }
    exact (inr (real_eq_trans (real_abs x) (real_opp x) c
                  (real_abs_neg_req x Hx0) Heq2)).
  - (* x == c ∧ −x < c ⟹ −x < x ⟹ 0 < x ⟹ |x| == x == c *)
    assert (Hox : real_lt (real_opp x) x).
    { exact (real_lt_eq_lt (real_opp x) c x Hlt2 (real_eq_sym x c Heq1)). }
    assert (Hx0 : real_lt real_zero x).
    { apply tw_lt_half.
      apply (real_lt_eq_lt real_zero
               (real_plus x (real_opp (real_opp x))) (real_plus x x)).
      + exact (real_lt_opp_plus (real_opp x) x Hox).
      + apply tw_ring_xopp_x. }
    exact (inr (real_eq_trans (real_abs x) x c (real_abs_pos_req x Hx0) Heq1)).
  - (* x == c ∧ −x == c ⟹ x == −x ⟹ x == 0 ⟹ |x| == 0 == c *)
    assert (Hxx : real_eq x (real_opp x)).
    { exact (real_eq_trans x c (real_opp x) Heq1 (real_eq_sym (real_opp x) c Heq2)). }
    pose (h2 := real_inv_pos (real_plus real_one real_one) real_two_pos).
    assert (Hinv : real_eq (real_mult (real_plus real_one real_one) h2) real_one).
    { unfold h2. apply real_inv_pos_correct. }
    assert (Hstep1 : real_eq x
                       (real_plus (real_mult x h2) (real_mult x h2))).
    { apply (real_eq_trans x
               (real_mult x (real_mult (real_plus real_one real_one) h2))
               (real_plus (real_mult x h2) (real_mult x h2))).
      - apply (real_eq_sym
                 (real_mult x (real_mult (real_plus real_one real_one) h2)) x).
        + apply (real_eq_trans
                   (real_mult x (real_mult (real_plus real_one real_one) h2))
                   (real_mult x real_one) x).
          * apply (RealSetoid.real_eq_mult_compat x
                     (real_mult (real_plus real_one real_one) h2)
                     x real_one).
            -- apply real_eq_refl.
            -- exact Hinv.
          * apply real_mult_one.
      - exact (real_eq_sym _ _ (tw_ring_two_split x h2)). }
    assert (Hstep2 : real_eq (real_mult x h2) (real_opp (real_mult x h2))).
    { apply (real_eq_trans (real_mult x h2)
               (real_mult (real_opp x) h2) _).
      - apply (RealSetoid.real_eq_mult_compat x h2 (real_opp x) h2 Hxx
                 (real_eq_refl h2)).
      - apply tw_ring_opp_mult. }
    assert (Hx0 : real_eq x real_zero).
    { exact (real_eq_trans x
               (real_plus (real_mult x h2) (real_mult x h2))
               real_zero
               Hstep1
               (real_eq_trans _
                  (real_plus (real_mult x h2) (real_opp (real_mult x h2)))
                  real_zero
                  (RealSetoid.real_eq_plus_compat (real_mult x h2)
                    (real_mult x h2) (real_mult x h2)
                    (real_opp (real_mult x h2)) (real_eq_refl _) Hstep2)
                  (real_plus_opp _))). }
    exact (inr (real_eq_trans (real_abs x) real_zero c
                  (real_eq_trans (real_abs x) (real_abs real_zero) real_zero
                     (real_abs_eq_compat x real_zero Hx0)
                     real_abs_zero_req)
                  (real_eq_sym c real_zero
                     (real_eq_trans c x real_zero (real_eq_sym x c Heq1) Hx0)))).
Qed.
(* ============================================================ *)
(* 5. T→∞ 半边追加席位（2026-09-06）：通用代数件与倒数唯一性     *)
(* ============================================================ *)

(* (a·b)·(c·d) == (a·c)·(b·d)（四因子重排） *)
Lemma tw_ring_abcd : forall a b c d : Real,
  real_eq (real_mult (real_mult a b) (real_mult c d))
          (real_mult (real_mult a c) (real_mult b d)).
Proof.
  intros a b c d.
  destruct a as [u1 Hu1]. destruct b as [u2 Hu2].
  destruct c as [v1 Hv1]. destruct d as [v2 Hv2].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (a·b)·c == (a·c)·b（中因子换位） *)
Lemma tw_ring_abc_acb : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult (real_mult a c) b).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (−x) + (x + −y) == −y *)
Lemma tw_ring_opp_xplus : forall x y : Real,
  real_eq (real_plus (real_opp x) (real_plus x (real_opp y))) (real_opp y).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < c ⟹ x < x + c（见证 e、N 直传，逐点 ring） *)
Lemma tw_lt_plus_r_zero : forall x c : Real,
  real_lt real_zero c -> real_lt x (real_plus x c).
Proof.
  intros x c H. destruct H as [e [He [N HN]]].
  destruct x as [u Hu]. destruct c as [v Hv].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    cbn [projT1 real_plus].
    apply Qlt_to_QltT.
    assert (Hq : Qlt e (v n - 0)) by (apply QltT_to_Qlt; exact (HN n Hn)).
    assert (Hz : u n + v n - u n == v n - 0) by ring.
    rewrite Hz. exact Hq.
Qed.

(* a ≤ b ⟹ −b ≤ −a（lt 支经差正性 + x < x + c；eq 支 opp 传输） *)
Lemma tw_le_opp_compat : forall a b : Real,
  real_le a b -> real_le (real_opp b) (real_opp a).
Proof.
  intros a b H. destruct H as [Hlt | Heq].
  - apply tw_lt_le.
    apply (real_lt_eq_lt (real_opp b)
             (real_plus (real_opp b) (real_plus b (real_opp a)))
             (real_opp a)).
    + apply tw_lt_plus_r_zero.
      exact (real_lt_opp_plus a b Hlt).
    + apply tw_ring_opp_xplus.
  - apply tw_eq_le.
    exact (real_eq_sym (real_opp a) (real_opp b)
             (RealSetoid.real_eq_opp_compat a b Heq)).
Qed.

(* 左乘保序：0 < c、a ≤ b ⟹ c·a ≤ c·b（镜像 real_le_mult_compat） *)
Lemma tw_le_mult_compat_l : forall a b c : Real,
  real_lt real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  apply (RealSetoid.real_le_id_l (real_mult c a) (real_mult a c) (real_mult c b)).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r (real_mult a c) (real_mult b c) (real_mult c b)).
    + apply real_mult_comm.
    + apply (real_le_mult_compat a b c Hc Hab).
Qed.

(* 倒数唯一性：x > 0、x·y == 1 ⟹ inv x == y
   链：inv x == inv x·1 == inv x·(x·y) == (inv x·x)·y
       == (x·inv x)·y == 1·y == y *)
Lemma tw_inv_unique : forall (x y : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x y) real_one -> real_eq (real_inv_pos x Hx) y.
Proof.
  intros x y Hx Hxy.
  apply (real_eq_trans (real_inv_pos x Hx)
           (real_mult (real_inv_pos x Hx) (real_mult x y)) y).
  - apply (real_eq_trans (real_inv_pos x Hx)
             (real_mult (real_inv_pos x Hx) real_one)
             (real_mult (real_inv_pos x Hx) (real_mult x y))).
    + apply real_eq_sym. apply real_mult_one.
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx) real_one
               (real_inv_pos x Hx) (real_mult x y)
               (real_eq_refl (real_inv_pos x Hx)) (real_eq_sym _ _ Hxy)).
  - apply (real_eq_trans (real_mult (real_inv_pos x Hx) (real_mult x y))
             (real_mult (real_mult (real_inv_pos x Hx) x) y) _).
    + apply real_mult_assoc.
    + apply (real_eq_trans (real_mult (real_mult (real_inv_pos x Hx) x) y)
               (real_mult real_one y) y).
      * apply (real_eq_trans (real_mult (real_mult (real_inv_pos x Hx) x) y)
                 (real_mult (real_mult x (real_inv_pos x Hx)) y)
                 (real_mult real_one y)).
        -- apply (RealSetoid.real_eq_mult_compat
                     (real_mult (real_inv_pos x Hx) x) y
                     (real_mult x (real_inv_pos x Hx)) y
                     (real_mult_comm (real_inv_pos x Hx) x) (real_eq_refl y)).
        -- apply (RealSetoid.real_eq_mult_compat
                     (real_mult x (real_inv_pos x Hx)) y real_one y
                     (real_inv_pos_correct x Hx) (real_eq_refl y)).
      * apply tw_ring_mult_one_l.
Qed.

(* ============================================================ *)
(* 6. list 求和序机器（泛型，Section 外）                        *)
(* ============================================================ *)

(* of_nat 非负 *)
Lemma tw_of_nat_nonneg : forall k : nat, real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_r real_zero
             (real_plus real_one (real_of_nat k))
             (real_of_nat (Datatypes.S k))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_le_id_l real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat k))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_le_plus_compat.
        -- apply tw_lt_le. apply real_lt_zero_one.
        -- exact IH.
Qed.

(* 非空表势正性 *)
Lemma tw_list_len_pos : forall (X : Set) (l : list X),
  Not (Id l nil) -> real_lt real_zero (real_of_nat (length l)).
Proof.
  intros X l. destruct l as [| w rest].
  - intro H. exact (match H (@id_refl (list X) nil) with end).
  - cbn [length]. intro Hn.
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest))) _).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply tw_of_nat_nonneg.
    + apply real_eq_refl.
Qed.

(* 逐点正 ⟹ 非空和正 *)
Lemma tw_sum_pos_nonempty : forall (X : Set) (f : X -> Real) (l : list X),
  (forall y : X, real_lt real_zero (f y)) -> Not (Id l nil) ->
  real_lt real_zero (real_list_sum X f l).
Proof.
  intros X f l. induction l as [| y rest IH]; intros Hf Hl.
  - exact (match Hl (@id_refl (list X) nil) with end).
  - destruct rest as [| y2 rest2].
    + cbn [real_list_sum].
      apply (real_lt_eq_lt real_zero (f y) (real_plus (f y) real_zero)).
      * apply Hf.
      * apply real_eq_sym. apply real_plus_zero.
    + cbn [real_list_sum].
      assert (Hpos : real_lt real_zero
                       (real_plus (f y)
                          (real_plus (f y2)
                             (real_list_sum X f rest2)))).
      { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
        - apply real_eq_sym. apply real_plus_zero.
        - apply real_lt_plus_compat.
          + apply Hf.
          + apply (IH Hf).
            intro Hc. inversion Hc. }
      apply (real_lt_eq_lt real_zero
               (real_plus (f y) (real_plus (f y2) (real_list_sum X f rest2))) _).
      * exact Hpos.
      * apply real_eq_refl.
Qed.

(* 逐点 ≤ c ⟹ Σ f ≤ N·c（镜像 sum_nonneg_le_const_aux） *)
Lemma tw_sum_le_const : forall (X : Set) (f : X -> Real) (c : Real) (l : list X),
  (forall z : X, InT z l -> real_le (f z) c) ->
  real_le (real_list_sum X f l) (real_mult (real_of_nat (length l)) c).
Proof.
  intros X f c l. induction l as [| x rest IH]; intro Hb.
  - exact (RealSetoid.real_eq_le real_zero
             (real_mult (real_of_nat (length (@nil X))) c)
             (real_eq_sym (real_mult real_zero c) real_zero
                (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                   real_zero (real_mult_comm real_zero c)
                   (real_mult_zero c)))).
  - cbn [real_list_sum length].
    apply (RealSetoid.real_le_id_r
             (real_plus (f x) (real_list_sum X f rest))
             (real_plus c (real_mult (real_of_nat (length rest)) c))
             (real_mult (real_of_nat (Datatypes.S (length rest))) c)).
    + apply (real_eq_trans
               (real_plus c (real_mult (real_of_nat (length rest)) c))
               (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat (length rest)) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (real_of_nat (length rest)) c)
                 (real_mult real_one c)
                 (real_mult (real_of_nat (length rest)) c)).
        -- apply (real_eq_trans c (real_mult c real_one)
                     (real_mult real_one c)
                     (real_eq_sym (real_mult c real_one) c (real_mult_one c))
                     (real_mult_comm c real_one)).
        -- apply real_eq_refl.
      * apply real_distrib_r.
    + apply real_le_plus_compat.
      * apply Hb. apply InT_here.
      * apply IH. intros z Hz. apply Hb. exact (InT_next z x rest Hz).
Qed.

(* 逐点 c ≤ f ⟹ N·c ≤ Σ f（下常数界，tw_sum_le_const 镜像） *)
Lemma tw_const_le_sum : forall (X : Set) (f : X -> Real) (c : Real) (l : list X),
  (forall z : X, InT z l -> real_le c (f z)) ->
  real_le (real_mult (real_of_nat (length l)) c) (real_list_sum X f l).
Proof.
  intros X f c l. induction l as [| x rest IH]; intro Hb.
  - exact (RealSetoid.real_eq_le
             (real_mult (real_of_nat (length (@nil X))) c)
             (real_list_sum X f (@nil X))
             (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                (real_list_sum X f (@nil X))
                (real_mult_comm real_zero c) (real_mult_zero c))).
  - cbn [real_list_sum length].
    apply (RealSetoid.real_le_id_l
             (real_mult (real_of_nat (Datatypes.S (length rest))) c)
             (real_plus c (real_mult (real_of_nat (length rest)) c))
             (real_plus (f x) (real_list_sum X f rest))).
    + apply (real_eq_trans
               (real_mult (real_of_nat (Datatypes.S (length rest))) c)
               (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat (length rest)) c)) _).
      * apply real_eq_sym. apply real_distrib_r.
      * apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                 (real_mult (real_of_nat (length rest)) c)
                 c (real_mult (real_of_nat (length rest)) c)).
        -- apply (real_eq_trans (real_mult real_one c) (real_mult c real_one) c
                     (real_mult_comm real_one c) (real_mult_one c)).
        -- apply real_eq_refl.
    + apply real_le_plus_compat.
      * apply Hb. apply InT_here.
      * apply IH. intros z Hz. apply Hb. exact (InT_next z x rest Hz).
Qed.

(* ============================================================ *)
(* 7. Section TempWindow：list 世界 + T→∞ 均匀极限主定理          *)
(* ============================================================ *)

Section TempWindow.

(* 世界：list 离散状态非空 + logits 双界（诚实接口，镜像 AttnHardLimit） *)
Variable Tok : Set.
Variable states : list Tok.
Variable states_nonempty : Not (Id states nil).
Variable zz : Tok -> Real.
Variable Delta : Real.
Variable Delta_pos : real_lt real_zero Delta.
Variable Hzz_lo : forall x : Tok, real_le (real_opp Delta) (zz x).
Variable Hzz_hi : forall x : Tok, real_le (zz x) Delta.

(* ---------- 7.1 温度化 softmax 分布与均匀分布 ---------- *)

(* 因子 e^{z(x)/T}（镜像 factor_T 形态） *)
Definition tw_factor (T : Real) (Ht : real_lt real_zero T) (x : Tok) : Real :=
  cauchy_real_exp (real_mult (real_inv_pos T Ht) (zz x)).

(* 配分函数 Z(T) = Σ states e^{z(x)/T} *)
Definition tw_ZT (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Tok (tw_factor T Ht) states.

Definition tw_ZT_pos (T : Real) (Ht : real_lt real_zero T) :
  real_lt real_zero (tw_ZT T Ht).
Proof.
  unfold tw_ZT. apply tw_sum_pos_nonempty.
  - intro x. apply cauchy_real_exp_pos.
  - exact states_nonempty.
Defined.

(* N = |states| > 0（透明件：进 real_inv_pos 计算位） *)
Definition tw_states_len_pos : real_lt real_zero (real_of_nat (length states)) :=
  tw_list_len_pos Tok states states_nonempty.

(* uniform(x) = 1/N *)
Definition tw_unif_dist : Real :=
  real_inv_pos (real_of_nat (length states)) tw_states_len_pos.

(* w_T(x) = e^{z(x)/T}/Z(T) *)
Definition tw_wT (T : Real) (Ht : real_lt real_zero T) (x : Tok) : Real :=
  real_mult (tw_factor T Ht x) (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)).

(* TV(w_T, U) = Σ_x |w_T(x) − 1/N| *)
Definition tv_unif (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Tok
    (fun x => real_abs (real_minus_r (tw_wT T Ht x) tw_unif_dist)) states.

(* 规范指数：u = Δ/T、u2 = 2Δ/T 与四个 exp 值 *)
Definition tw_u (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_mult (real_inv_pos T Ht) Delta.
Definition tw_u2 (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_mult (real_plus Delta Delta) (real_inv_pos T Ht).
Definition tw_EU (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (tw_u T Ht).
Definition tw_EL (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (tw_u T Ht)).
Definition tw_E2 (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (tw_u2 T Ht).
Definition tw_E2L (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (tw_u2 T Ht)).

(* ---------- 7.2 正性与指数恒等式 ---------- *)

Lemma tw_u2_pos : forall T Ht, real_lt real_zero (tw_u2 T Ht).
Proof.
  intros T Ht.
  assert (H2D : real_lt real_zero (real_plus Delta Delta)).
  { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
             (real_plus Delta Delta)).
    - apply real_eq_sym. apply real_plus_zero.
    - exact (real_lt_plus_compat real_zero Delta real_zero Delta
               Delta_pos Delta_pos). }
  unfold tw_u2.
  apply (real_mult_pos_compat (real_plus Delta Delta) (real_inv_pos T Ht)).
  - exact H2D.
  - apply real_inv_pos_pos.
Qed.

(* u + u == u2：invT·Δ + invT·Δ == (Δ+Δ)·invT *)
Lemma tw_uu_eq_u2 : forall T Ht,
  real_eq (real_plus (tw_u T Ht) (tw_u T Ht)) (tw_u2 T Ht).
Proof.
  intros T Ht. unfold tw_u, tw_u2.
  apply (real_eq_trans
           (real_plus (real_mult (real_inv_pos T Ht) Delta)
                      (real_mult (real_inv_pos T Ht) Delta))
           (real_plus (real_mult Delta (real_inv_pos T Ht))
                      (real_mult Delta (real_inv_pos T Ht)))
           (real_mult (real_plus Delta Delta) (real_inv_pos T Ht))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_inv_pos T Ht) Delta)
             (real_mult (real_inv_pos T Ht) Delta)
             (real_mult Delta (real_inv_pos T Ht))
             (real_mult Delta (real_inv_pos T Ht))
             (real_mult_comm (real_inv_pos T Ht) Delta)
             (real_mult_comm (real_inv_pos T Ht) Delta)).
  - apply real_eq_sym. apply tw_ring_dd_mult.
Qed.

(* e^u·e^u == e^{u2} *)
Lemma tw_EU_EU_eq_E2 : forall T Ht,
  real_eq (real_mult (tw_EU T Ht) (tw_EU T Ht)) (tw_E2 T Ht).
Proof.
  intros T Ht.
  apply (real_eq_trans (real_mult (tw_EU T Ht) (tw_EU T Ht))
           (cauchy_real_exp (real_plus (tw_u T Ht) (tw_u T Ht))) (tw_E2 T Ht)).
  - apply real_eq_sym. apply (cauchy_real_exp_plus (tw_u T Ht) (tw_u T Ht)).
  - apply cauchy_real_exp_wd. exact (tw_uu_eq_u2 T Ht).
Qed.

(* e^{−u}·e^{−u} == e^{−u2} *)
Lemma tw_EL_EL_eq_E2L : forall T Ht,
  real_eq (real_mult (tw_EL T Ht) (tw_EL T Ht)) (tw_E2L T Ht).
Proof.
  intros T Ht.
  apply (real_eq_trans (real_mult (tw_EL T Ht) (tw_EL T Ht))
           (cauchy_real_exp
              (real_plus (real_opp (tw_u T Ht)) (real_opp (tw_u T Ht))))
           (tw_E2L T Ht)).
  - apply real_eq_sym.
    apply (cauchy_real_exp_plus (real_opp (tw_u T Ht)) (real_opp (tw_u T Ht))).
  - apply cauchy_real_exp_wd.
    apply (real_eq_trans
             (real_plus (real_opp (tw_u T Ht)) (real_opp (tw_u T Ht)))
             (real_opp (real_plus (tw_u T Ht) (tw_u T Ht)))
             (real_opp (tw_u2 T Ht))).
    + apply real_eq_sym. apply real_opp_plus.
    + apply (RealSetoid.real_eq_opp_compat (real_plus (tw_u T Ht) (tw_u T Ht))
               (tw_u2 T Ht)).
      exact (tw_uu_eq_u2 T Ht).
Qed.

(* ---------- 7.3 逐点 exp 夹逼 ---------- *)

Lemma tw_EL_le_factor : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (tw_EL T Ht) (tw_factor T Ht x).
Proof.
  intros T Ht x. unfold tw_EL, tw_factor, tw_u.
  apply tw_exp_mono_le.
  apply (RealSetoid.real_le_id_l (real_opp (real_mult (real_inv_pos T Ht) Delta))
           (real_mult (real_opp Delta) (real_inv_pos T Ht))
           (real_mult (real_inv_pos T Ht) (zz x))).
  - apply (real_eq_trans (real_opp (real_mult (real_inv_pos T Ht) Delta))
             (real_opp (real_mult Delta (real_inv_pos T Ht)))
             (real_mult (real_opp Delta) (real_inv_pos T Ht))).
    + apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos T Ht) Delta)
               (real_mult Delta (real_inv_pos T Ht))).
      apply real_mult_comm.
    + apply real_eq_sym. apply tw_ring_opp_mult.
  - apply (real_le_trans (real_mult (real_opp Delta) (real_inv_pos T Ht))
             (real_mult (zz x) (real_inv_pos T Ht))
             (real_mult (real_inv_pos T Ht) (zz x))).
    + apply (real_le_mult_compat (real_opp Delta) (zz x)
               (real_inv_pos T Ht) (real_inv_pos_pos T Ht) (Hzz_lo x)).
    + apply (RealSetoid.real_eq_le _ _
               (real_mult_comm (zz x) (real_inv_pos T Ht))).
Qed.

Lemma tw_factor_le_EU : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (tw_factor T Ht x) (tw_EU T Ht).
Proof.
  intros T Ht x. unfold tw_EU, tw_factor, tw_u.
  apply tw_exp_mono_le.
  apply (real_le_trans (real_mult (real_inv_pos T Ht) (zz x))
           (real_mult (zz x) (real_inv_pos T Ht))
           (real_mult (real_inv_pos T Ht) Delta)).
  - apply (RealSetoid.real_eq_le _ _
             (real_mult_comm (real_inv_pos T Ht) (zz x))).
  - apply (real_le_trans (real_mult (zz x) (real_inv_pos T Ht))
             (real_mult Delta (real_inv_pos T Ht))
             (real_mult (real_inv_pos T Ht) Delta)).
    + apply (real_le_mult_compat (zz x) Delta
               (real_inv_pos T Ht) (real_inv_pos_pos T Ht) (Hzz_hi x)).
    + apply (RealSetoid.real_eq_le _ _
               (real_mult_comm Delta (real_inv_pos T Ht))).
Qed.

(* ---------- 7.4 配分函数双侧界与 inv 三明治 ---------- *)

Lemma tw_ZT_ge_NEL : forall T Ht,
  real_le (real_mult (real_of_nat (length states)) (tw_EL T Ht)) (tw_ZT T Ht).
Proof.
  intros T Ht. unfold tw_ZT. apply tw_const_le_sum.
  intros x _. apply tw_EL_le_factor.
Qed.

Lemma tw_ZT_le_NEU : forall T Ht,
  real_le (tw_ZT T Ht)
          (real_mult (real_of_nat (length states)) (tw_EU T Ht)).
Proof.
  intros T Ht. unfold tw_ZT. apply tw_sum_le_const.
  intros x _. apply tw_factor_le_EU.
Qed.

(* inv Z ≤ invN·e^{Δ/T}：Z ≥ N·e^{−Δ/T} 反单调 + inv 唯一性 *)
Lemma tw_invZ_le_EUinvN : forall T Ht,
  real_le (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
          (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EU T Ht)).
Proof.
  intros T Ht.
  assert (HZge : real_le (real_mult (real_of_nat (length states))
                            (tw_EL T Ht)) (tw_ZT T Ht))
    by exact (tw_ZT_ge_NEL T Ht).
  assert (Hple : real_lt real_zero
                   (real_mult (real_of_nat (length states)) (tw_EL T Ht)))
    by (apply (real_mult_pos_compat (real_of_nat (length states))
                 (tw_EL T Ht));
        [exact tw_states_len_pos | apply cauchy_real_exp_pos]).
  assert (Hinv : real_le (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
                   (real_inv_pos (real_mult (real_of_nat (length states))
                                       (tw_EL T Ht)) Hple))
    by exact (real_inv_pos_le_compat (real_mult (real_of_nat (length states))
                          (tw_EL T Ht)) (tw_ZT T Ht) Hple
                 (tw_ZT_pos T Ht) HZge).
  assert (Hid : real_eq (real_inv_pos (real_mult (real_of_nat (length states))
                                     (tw_EL T Ht)) Hple)
                  (real_mult (real_inv_pos (real_of_nat (length states))
                              tw_states_len_pos) (tw_EU T Ht))).
  { apply (tw_inv_unique (real_mult (real_of_nat (length states))
                            (tw_EL T Ht))
             (real_mult (real_inv_pos (real_of_nat (length states))
                         tw_states_len_pos) (tw_EU T Ht)) Hple).
    apply (real_eq_trans
             (real_mult (real_mult (real_of_nat (length states))
                          (tw_EL T Ht))
                       (real_mult (real_inv_pos (real_of_nat (length states))
                                   tw_states_len_pos) (tw_EU T Ht)))
             (real_mult
                (real_mult (real_of_nat (length states))
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos))
                (real_mult (tw_EL T Ht) (tw_EU T Ht)))
             real_one).
    - apply tw_ring_abcd.
    - apply (real_eq_trans _ (real_mult real_one real_one) real_one).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_of_nat (length states))
                    (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos))
                 (real_mult (tw_EL T Ht) (tw_EU T Ht))
                 real_one real_one
                 (real_inv_pos_correct (real_of_nat (length states))
                    tw_states_len_pos)
                 (tw_exp_opp_prod (tw_u T Ht))).
      + apply real_mult_one. }
  exact (tw_le_eq_r
           (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
           (real_inv_pos (real_mult (real_of_nat (length states))
                              (tw_EL T Ht)) Hple)
           (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EU T Ht))
           Hinv Hid).
Qed.

(* invN·e^{−Δ/T} ≤ inv Z：Z ≤ N·e^{Δ/T} 反单调 + inv 唯一性 *)
Lemma tw_ELinvN_le_invZ : forall T Ht,
  real_le (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EL T Ht))
          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)).
Proof.
  intros T Ht.
  assert (HZle : real_le (tw_ZT T Ht)
                   (real_mult (real_of_nat (length states)) (tw_EU T Ht)))
    by exact (tw_ZT_le_NEU T Ht).
  assert (Hpue : real_lt real_zero
                   (real_mult (real_of_nat (length states)) (tw_EU T Ht)))
    by (apply (real_mult_pos_compat (real_of_nat (length states))
                 (tw_EU T Ht));
        [exact tw_states_len_pos | apply cauchy_real_exp_pos]).
  assert (Hinv : real_le (real_inv_pos (real_mult (real_of_nat (length states))
                                     (tw_EU T Ht)) Hpue)
                   (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
    by exact (real_inv_pos_le_compat (tw_ZT T Ht)
                (real_mult (real_of_nat (length states)) (tw_EU T Ht))
                (tw_ZT_pos T Ht) Hpue HZle).
  assert (Hid : real_eq (real_inv_pos (real_mult (real_of_nat (length states))
                                     (tw_EU T Ht)) Hpue)
                  (real_mult (real_inv_pos (real_of_nat (length states))
                              tw_states_len_pos) (tw_EL T Ht))).
  { apply (tw_inv_unique (real_mult (real_of_nat (length states))
                            (tw_EU T Ht))
             (real_mult (real_inv_pos (real_of_nat (length states))
                         tw_states_len_pos) (tw_EL T Ht)) Hpue).
    apply (real_eq_trans
             (real_mult (real_mult (real_of_nat (length states))
                          (tw_EU T Ht))
                       (real_mult (real_inv_pos (real_of_nat (length states))
                                   tw_states_len_pos) (tw_EL T Ht)))
             (real_mult
                (real_mult (real_of_nat (length states))
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos))
                (real_mult (tw_EU T Ht) (tw_EL T Ht)))
             real_one).
    - apply tw_ring_abcd.
    - apply (real_eq_trans _ (real_mult real_one real_one) real_one).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_of_nat (length states))
                    (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos))
                 (real_mult (tw_EU T Ht) (tw_EL T Ht))
                 real_one real_one
                 (real_inv_pos_correct (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_eq_trans (real_mult (tw_EU T Ht) (tw_EL T Ht))
                    (real_mult (tw_EL T Ht) (tw_EU T Ht)) real_one
                    (real_mult_comm (tw_EU T Ht) (tw_EL T Ht))
                    (tw_exp_opp_prod (tw_u T Ht)))).
      + apply real_mult_one. }
  exact (tw_le_eq_l
           (real_inv_pos (real_mult (real_of_nat (length states))
                              (tw_EU T Ht)) Hpue)
           (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
           (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EL T Ht))
           Hinv Hid).
Qed.

(* ---------- 7.5 逐点 w 界与逐点绝对值界 ---------- *)

(* w_T(x) ≤ e^{2Δ/T}·(1/N) *)
Lemma tw_wT_le_E2invN : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (tw_wT T Ht x)
          (real_mult (tw_E2 T Ht)
             (real_inv_pos (real_of_nat (length states)) tw_states_len_pos)).
Proof.
  intros T Ht x.
  assert (HinvZ : real_lt real_zero
                    (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
    by apply real_inv_pos_pos.
  assert (HEU : real_lt real_zero (tw_EU T Ht)) by apply cauchy_real_exp_pos.
  assert (H1 : real_le (real_mult (tw_factor T Ht x)
                         (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
                       (real_mult (tw_EU T Ht)
                          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))))
    by exact (real_le_mult_compat (tw_factor T Ht x) (tw_EU T Ht)
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)) HinvZ
                (tw_factor_le_EU T Ht x)).
  assert (H2 : real_le (real_mult (tw_EU T Ht)
                         (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
                       (real_mult (tw_EU T Ht)
                          (real_mult (real_inv_pos (real_of_nat (length states))
                                      tw_states_len_pos) (tw_EU T Ht))))
    by exact (tw_le_mult_compat_l
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EU T Ht))
                (tw_EU T Ht) HEU (tw_invZ_le_EUinvN T Ht)).
  assert (Hid : real_eq (real_mult (tw_EU T Ht)
                          (real_mult (real_inv_pos (real_of_nat (length states))
                                      tw_states_len_pos) (tw_EU T Ht)))
                  (real_mult (tw_E2 T Ht)
                     (real_inv_pos (real_of_nat (length states))
                        tw_states_len_pos))).
  { apply (real_eq_trans
             (real_mult (tw_EU T Ht)
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EU T Ht)))
             (real_mult (real_mult (tw_EU T Ht)
                          (real_inv_pos (real_of_nat (length states))
                             tw_states_len_pos)) (tw_EU T Ht))
             (real_mult (tw_E2 T Ht)
                (real_inv_pos (real_of_nat (length states))
                   tw_states_len_pos))).
    - apply real_mult_assoc.
    - apply (real_eq_trans
               (real_mult (real_mult (tw_EU T Ht)
                            (real_inv_pos (real_of_nat (length states))
                               tw_states_len_pos)) (tw_EU T Ht))
               (real_mult (real_mult (tw_EU T Ht) (tw_EU T Ht))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos)) _).
      + apply tw_ring_abc_acb.
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (tw_EU T Ht) (tw_EU T Ht))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (tw_E2 T Ht)
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (tw_EU_EU_eq_E2 T Ht) (real_eq_refl _)). }
  apply (real_le_trans (real_mult (tw_factor T Ht x)
                            (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
           (real_mult (tw_EU T Ht)
              (real_mult (real_inv_pos (real_of_nat (length states))
                          tw_states_len_pos) (tw_EU T Ht)))
           (real_mult (tw_E2 T Ht)
              (real_inv_pos (real_of_nat (length states))
                 tw_states_len_pos))).
  - exact (real_le_trans _ _ _ H1 H2).
  - exact (RealSetoid.real_eq_le _ _ Hid).
Qed.

(* e^{−2Δ/T}·(1/N) ≤ w_T(x) *)
Lemma tw_E2LinvN_le_wT : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (real_mult (tw_E2L T Ht)
             (real_inv_pos (real_of_nat (length states)) tw_states_len_pos))
          (tw_wT T Ht x).
Proof.
  intros T Ht x.
  assert (HinvZ : real_lt real_zero
                    (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
    by apply real_inv_pos_pos.
  assert (HEL : real_lt real_zero (tw_EL T Ht)) by apply cauchy_real_exp_pos.
  assert (Hid : real_eq (real_mult (tw_E2L T Ht)
                          (real_inv_pos (real_of_nat (length states))
                             tw_states_len_pos))
                  (real_mult (tw_EL T Ht)
                     (real_mult (real_inv_pos (real_of_nat (length states))
                                 tw_states_len_pos) (tw_EL T Ht)))).
  { apply (real_eq_trans
             (real_mult (tw_E2L T Ht)
                (real_inv_pos (real_of_nat (length states))
                   tw_states_len_pos))
             (real_mult (tw_EL T Ht)
                (real_mult (tw_EL T Ht)
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos)))
             (real_mult (tw_EL T Ht)
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EL T Ht)))).
    - apply (real_eq_trans
               (real_mult (tw_E2L T Ht)
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_mult (real_mult (tw_EL T Ht) (tw_EL T Ht))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_mult (tw_EL T Ht)
                  (real_mult (tw_EL T Ht)
                     (real_inv_pos (real_of_nat (length states))
                        tw_states_len_pos)))).
      + apply (RealSetoid.real_eq_mult_compat
                 (tw_E2L T Ht)
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_mult (tw_EL T Ht) (tw_EL T Ht))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_eq_sym _ _ (tw_EL_EL_eq_E2L T Ht)) (real_eq_refl _)).
      + apply real_eq_sym.
        exact (real_mult_assoc (tw_EL T Ht) (tw_EL T Ht)
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)).
    - apply (RealSetoid.real_eq_mult_compat
               (tw_EL T Ht)
               (real_mult (tw_EL T Ht)
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (tw_EL T Ht)
               (real_mult (real_inv_pos (real_of_nat (length states))
                           tw_states_len_pos) (tw_EL T Ht))
               (real_eq_refl (tw_EL T Ht))
               (real_mult_comm (tw_EL T Ht)
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))). }
  assert (H2 : real_le (real_mult (tw_EL T Ht)
                         (real_mult (real_inv_pos (real_of_nat (length states))
                                     tw_states_len_pos) (tw_EL T Ht)))
                       (real_mult (tw_EL T Ht)
                          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))))
    by exact (tw_le_mult_compat_l
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EL T Ht))
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
                (tw_EL T Ht) HEL (tw_ELinvN_le_invZ T Ht)).
  assert (H3 : real_le (real_mult (tw_EL T Ht)
                         (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
                       (real_mult (tw_factor T Ht x)
                          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))))
    by exact (real_le_mult_compat (tw_EL T Ht) (tw_factor T Ht x)
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)) HinvZ
                (tw_EL_le_factor T Ht x)).
  apply (real_le_trans
           (real_mult (tw_E2L T Ht)
              (real_inv_pos (real_of_nat (length states))
                 tw_states_len_pos))
           (real_mult (tw_EL T Ht)
              (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
           (tw_wT T Ht x)).
  - exact (RealSetoid.real_le_id_l _ _ _ Hid H2).
  - exact H3.
Qed.

(* 逐点绝对值界：|w_T(x) − 1/N| ≤ (e^{2Δ/T} − 1)/N
   tw_abs_le 收口：上支 w−1/N ≤ (E2−1)/N（tw_ring_sub_mult 换形）；
   下支 1/N−w ≤ (1−e^{−2Δ/T})/N ≤ (E2−1)/N
   （tw_ring_sub_mult_l + tw_one_minus_exp_le） *)
Lemma tw_h_le : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (real_abs (real_minus_r (tw_wT T Ht x) tw_unif_dist))
          (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
             tw_unif_dist).
Proof.
  intros T Ht x.
  assert (HinvN : real_lt real_zero tw_unif_dist)
    by (unfold tw_unif_dist; apply real_inv_pos_pos).
  apply tw_abs_le.
  - apply (tw_le_eq_r (real_minus_r (tw_wT T Ht x) tw_unif_dist)
             (real_plus (real_mult (tw_E2 T Ht) tw_unif_dist)
                (real_opp tw_unif_dist))
             (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                tw_unif_dist)).
    + apply real_le_plus_compat;
        [exact (tw_wT_le_E2invN T Ht x) | apply real_le_refl].
    + exact (tw_ring_sub_mult (tw_E2 T Ht) tw_unif_dist).
  - apply (tw_le_eq_l (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))
             (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                tw_unif_dist)
             (real_opp (real_minus_r (tw_wT T Ht x) tw_unif_dist))).
    + apply (real_le_trans (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))
               (real_plus tw_unif_dist
                  (real_opp (real_mult (tw_E2L T Ht) tw_unif_dist)))
               (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                  tw_unif_dist)).
      * apply real_le_plus_compat.
        -- apply real_le_refl.
        -- apply tw_le_opp_compat.
           exact (tw_E2LinvN_le_wT T Ht x).
      * apply (real_le_trans
                 (real_plus tw_unif_dist
                    (real_opp (real_mult (tw_E2L T Ht) tw_unif_dist)))
                 (real_mult (real_plus real_one (real_opp (tw_E2L T Ht)))
                    tw_unif_dist)
                 (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                    tw_unif_dist)).
        -- exact (RealSetoid.real_eq_le _ _
                     (tw_ring_sub_mult_l (tw_E2L T Ht) tw_unif_dist)).
        -- exact (real_le_mult_compat
                    (real_plus real_one (real_opp (tw_E2L T Ht)))
                    (real_plus (tw_E2 T Ht) (real_opp real_one))
                    tw_unif_dist HinvN
                    (tw_one_minus_exp_le (tw_u2 T Ht) (tw_u2_pos T Ht))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_opp (real_minus_r (tw_wT T Ht x) tw_unif_dist))
               (real_plus (real_opp (tw_wT T Ht x))
                  (real_opp (real_opp tw_unif_dist)))
               (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))).
      * apply real_opp_plus.
      * apply (real_eq_trans
                 (real_plus (real_opp (tw_wT T Ht x))
                    (real_opp (real_opp tw_unif_dist)))
                 (real_plus (real_opp (tw_wT T Ht x)) tw_unif_dist)
                 (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_opp (tw_wT T Ht x))
                     (real_opp (real_opp tw_unif_dist))
                     (real_opp (tw_wT T Ht x)) tw_unif_dist
                     (real_eq_refl _) (real_opp_opp tw_unif_dist)).
        -- apply real_plus_comm.
Qed.

(* ---------- 7.6 求和收口：tv_unif ≤ e^{2Δ/T} − 1 ---------- *)

Lemma tv_unif_le : forall T Ht,
  real_le (tv_unif T Ht) (real_plus (tw_E2 T Ht) (real_opp real_one)).
Proof.
  intros T Ht.
  assert (Hmid : real_le
                   (real_mult (real_of_nat (length states))
                      (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                         (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos)))
                   (real_plus (tw_E2 T Ht) (real_opp real_one))).
  { apply (RealSetoid.real_eq_le).
    apply (real_eq_trans
             (real_mult (real_of_nat (length states))
                (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos)))
             (real_mult
                (real_mult (real_of_nat (length states))
                   (real_plus (tw_E2 T Ht) (real_opp real_one)))
                (real_inv_pos (real_of_nat (length states))
                   tw_states_len_pos))
             (real_plus (tw_E2 T Ht) (real_opp real_one))).
    - apply real_mult_assoc.
    - apply (real_eq_trans
               (real_mult
                  (real_mult (real_of_nat (length states))
                     (real_plus (tw_E2 T Ht) (real_opp real_one)))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_mult
                  (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                     (real_of_nat (length states)))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_plus (tw_E2 T Ht) (real_opp real_one))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_of_nat (length states))
                    (real_plus (tw_E2 T Ht) (real_opp real_one)))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                    (real_of_nat (length states)))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_mult_comm (real_of_nat (length states))
                    (real_plus (tw_E2 T Ht) (real_opp real_one)))
                 (real_eq_refl _)).
      + apply (real_eq_trans
                 (real_mult
                    (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                       (real_of_nat (length states)))
                    (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos))
                 (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                    (real_mult (real_of_nat (length states))
                       (real_inv_pos (real_of_nat (length states))
                          tw_states_len_pos)))
                 (real_plus (tw_E2 T Ht) (real_opp real_one))).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (real_eq_trans
                   (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                      (real_mult (real_of_nat (length states))
                         (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos)))
                   (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                      real_one)
                   (real_plus (tw_E2 T Ht) (real_opp real_one))).
          -- apply (RealSetoid.real_eq_mult_compat
                       (real_plus (tw_E2 T Ht) (real_opp real_one))
                       (real_mult (real_of_nat (length states))
                          (real_inv_pos (real_of_nat (length states))
                             tw_states_len_pos))
                       (real_plus (tw_E2 T Ht) (real_opp real_one)) real_one
                       (real_eq_refl _)
                       (real_inv_pos_correct (real_of_nat (length states))
                          tw_states_len_pos)).
          -- apply real_mult_one. }
  apply (real_le_trans (tv_unif T Ht)
           (real_mult (real_of_nat (length states))
              (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)))
           (real_plus (tw_E2 T Ht) (real_opp real_one))).
  - unfold tv_unif. apply tw_sum_le_const.
    intros x _. apply tw_h_le.
  - exact Hmid.
Qed.

(* ---------- 7.7 主定理：量词翻转 ---------- *)

(*   T₂ := 2Δ·inv(cw_log(1+eps)) + 1 > 0；
     T > T₂ ⟹ 2Δ/T < cw_log(1+eps) ⟹ e^{2Δ/T} < 1+eps
     ⟹ tv_unif ≤ e^{2Δ/T} − 1 ≤ (1+eps) − 1 = eps。 *)
Theorem temp_window_T_infty :
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun T2 => And (real_lt real_zero T2)
         (forall (T : Real) (Ht : real_lt real_zero T), real_lt T2 T ->
          real_le (tv_unif T Ht) eps)).
Proof.
  intros eps Heps.
  pose (U := real_plus real_one eps).
  (* 1 < U ⟹ 0 < U ⟹ L := cw_log U > 0 *)
  assert (HU1 : real_lt real_one U).
  { apply (real_eq_lt_lt real_one (real_plus real_zero real_one) U).
    - apply (real_eq_trans real_one (real_plus real_one real_zero)
               (real_plus real_zero real_one)).
      + apply real_eq_sym. apply real_plus_zero.
      + apply real_plus_comm.
    - apply (real_lt_eq_lt (real_plus real_zero real_one)
               (real_plus eps real_one) U).
      + exact (real_lt_plus_compat_lt_le real_zero eps real_one real_one
                 Heps (real_le_refl real_one)).
      + apply real_plus_comm. }
  assert (HUpos : real_lt real_zero U)
    by exact (real_lt_trans real_zero real_one U real_lt_zero_one HU1).
  assert (HL0 : real_lt real_zero (cw_log U HUpos)).
  { apply (real_eq_lt_lt real_zero (cw_log real_one real_lt_zero_one)
             (cw_log U HUpos)).
    - apply real_eq_sym. apply log_inv_one_thm.
    - exact (real_log_lt_mono real_one U real_lt_zero_one HUpos HU1). }
  pose (L := cw_log U HUpos).
  pose (invL := real_inv_pos L HL0).
  pose (twoD := real_plus Delta Delta).
  assert (H2D : real_lt real_zero twoD)
    by (apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) twoD);
        [apply real_eq_sym; apply real_plus_zero |
         exact (real_lt_plus_compat real_zero Delta real_zero Delta
                   Delta_pos Delta_pos)]).
  assert (HinvL : real_lt real_zero invL) by apply real_inv_pos_pos.
  assert (H2DinvL : real_lt real_zero (real_mult twoD invL))
    by (apply (real_mult_pos_compat twoD invL); [exact H2D | exact HinvL]).
  exists (real_plus (real_mult twoD invL) real_one).
  split.
  - (* T₂ = 2Δ·invL + 1 > 0：0 < 1 ≤ T₂ *)
    apply (real_lt_le_trans real_zero real_one
             (real_plus (real_mult twoD invL) real_one) real_lt_zero_one).
    apply (tw_le_eq_l (real_plus real_zero real_one)
             (real_plus (real_mult twoD invL) real_one) real_one).
    + apply real_le_plus_compat.
      * apply tw_lt_le. exact H2DinvL.
      * apply real_le_refl.
    + apply (real_eq_trans real_one (real_plus real_one real_zero)
               (real_plus real_zero real_one)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_plus_comm.
  - intros T Ht HT2T.
    (* T·L 与 (2Δ+L) 的竞争：T₂·L == 2Δ + L *)
    assert (Ha : real_lt (real_mult (real_plus (real_mult twoD invL) real_one) L)
                   (real_mult T L))
      by exact (real_mult_lt_compat
                  (real_plus (real_mult twoD invL) real_one) T L HT2T HL0).
    assert (Hb : real_eq (real_mult (real_plus (real_mult twoD invL) real_one) L)
                           (real_plus twoD L)).
    { apply (real_eq_trans
               (real_mult (real_plus (real_mult twoD invL) real_one) L)
               (real_plus (real_mult twoD (real_mult L invL)) L)
               (real_plus twoD L)).
      - apply (real_eq_trans
                 (real_mult (real_plus (real_mult twoD invL) real_one) L)
                 (real_mult L (real_plus (real_mult twoD invL) real_one))
                 (real_plus (real_mult twoD (real_mult L invL)) L)).
        + apply real_mult_comm.
        + exact (tw_ring_t2 Delta L invL).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult twoD (real_mult L invL)) L twoD L).
        + apply (real_eq_trans (real_mult twoD (real_mult L invL))
                   (real_mult twoD real_one) twoD).
          * apply (RealSetoid.real_eq_mult_compat twoD (real_mult L invL)
                     twoD real_one (real_eq_refl twoD)
                     (real_inv_pos_correct L HL0)).
          * apply real_mult_one.
        + apply real_eq_refl. }
    assert (Hc : real_lt (real_plus twoD L) (real_mult T L))
      by exact (real_eq_lt_lt (real_plus twoD L)
                  (real_mult (real_plus (real_mult twoD invL) real_one) L)
                  (real_mult T L) (real_eq_sym _ _ Hb) Ha).
    assert (HinvT : real_lt real_zero (real_inv_pos T Ht))
      by apply real_inv_pos_pos.
    assert (Hd : real_lt (real_mult (real_plus twoD L) (real_inv_pos T Ht))
                           (real_mult (real_mult T L) (real_inv_pos T Ht)))
      by exact (real_mult_lt_compat (real_plus twoD L) (real_mult T L)
                  (real_inv_pos T Ht) Hc HinvT).
    assert (He : real_eq (real_mult (real_mult T L) (real_inv_pos T Ht)) L).
    { apply (real_eq_trans
               (real_mult (real_mult T L) (real_inv_pos T Ht))
               (real_mult (real_mult T (real_inv_pos T Ht)) L) L).
      - apply tw_ring_abc_acb.
      - apply (real_eq_trans
                 (real_mult (real_mult T (real_inv_pos T Ht)) L)
                 (real_mult real_one L) L).
        + apply (RealSetoid.real_eq_mult_compat
                   (real_mult T (real_inv_pos T Ht)) L real_one L
                   (real_inv_pos_correct T Ht) (real_eq_refl L)).
        + apply tw_ring_mult_one_l. }
    assert (Hf : real_lt (real_mult (real_plus twoD L) (real_inv_pos T Ht)) L)
      by exact (real_lt_eq_lt (real_mult (real_plus twoD L)
                                   (real_inv_pos T Ht))
                  (real_mult (real_mult T L) (real_inv_pos T Ht)) L Hd He).
    (* (2Δ+L)·invT == 2Δ/T + L/T，且 L/T > 0 ⟹ 2Δ/T < L *)
    assert (HddT : real_eq (real_mult (real_plus twoD L) (real_inv_pos T Ht))
                             (real_plus (tw_u2 T Ht)
                                (real_mult L (real_inv_pos T Ht))))
      by exact (tw_ring_ddl Delta L (real_inv_pos T Ht)).
    assert (HLiT : real_lt real_zero (real_mult L (real_inv_pos T Ht)))
      by (apply (real_mult_pos_compat L (real_inv_pos T Ht));
          [exact HL0 | exact HinvT]).
    assert (Hh : real_lt (real_plus (tw_u2 T Ht)
                              (real_mult L (real_inv_pos T Ht))) L)
      by exact (real_eq_lt_lt (real_plus (tw_u2 T Ht)
                                (real_mult L (real_inv_pos T Ht)))
                  (real_mult (real_plus twoD L) (real_inv_pos T Ht)) L
                  (real_eq_sym _ _ HddT) Hf).
    assert (Hi : real_lt (tw_u2 T Ht) L).
    { apply (real_lt_trans (tw_u2 T Ht)
               (real_plus (tw_u2 T Ht) (real_mult L (real_inv_pos T Ht))) L).
      - apply tw_lt_plus_r_zero. exact HLiT.
      - exact Hh. }
    (* e^{2Δ/T} < e^L == 1 + eps *)
    assert (Hj : real_lt (tw_E2 T Ht) U)
      by exact (real_lt_eq_lt (tw_E2 T Ht) (cauchy_real_exp L) U
                  (cauchy_real_exp_mono (tw_u2 T Ht) L Hi)
                  (cw_log_exp_right U HUpos)).
    (* 收口：tv ≤ E2 − 1 ≤ U − 1 == eps *)
    apply (real_le_trans (tv_unif T Ht)
             (real_plus (tw_E2 T Ht) (real_opp real_one)) eps).
    + exact (tv_unif_le T Ht).
    + apply (tw_le_eq_r (real_plus (tw_E2 T Ht) (real_opp real_one))
               (real_plus U (real_opp real_one)) eps).
      * apply real_le_plus_compat; [exact (inl Hj) | apply real_le_refl].
      * exact (tw_ring_one_eps_minus eps).
Qed.

End TempWindow.

(* ---------- UpKVEv ---------- *)
(* ============================================================ *)
(* UpKVEv.v — 方案四拆分前半：K_ev 逐出核机器（机器层）          *)
(*   世界定义 + 行归一化 + minorization 传送。                   *)
(*   全部 Set 层（Id/And/Or/Not/InT/sigT），语句零 Prop 泄露。   *)
(*   构造性：无外部假设，仅依赖 CW_ConstructiveWorld_219。       *)
(*                                                              *)
(*   接口契约（与并行席对齐，逐字）：                            *)
(*     Z_keep    ：keep 过滤行和 Σ if keep then K else 0        *)
(*     Z_keep_pos：HZk_pos 升级为定理（由 keep_nonempty+Kpos    *)
(*                 + single_le_sum_aux 构造性放电，报告已注明）  *)
(*     K_ev      ：if keep s' then K·inv(Z_keep s) else 0       *)
(*     件 0 Z_keep_le_one         ：Z_keep s ≤ 1                *)
(*     件 1 kev_row_normalized    ：行和 == 1                   *)
(*     件 2 kev_minorization      ：δ·U(s') ≤ K_ev s s'         *)
(*     件 2b kev_drop_zero / uncond 版                          *)
(*   δ 形态：Section Variable（delta_pos + delta_le_one +       *)
(*   delta_minor : δ·U ≤ K 逐点——对齐 AttnDoeblin.v 的          *)
(*   minorization 前提先例；仅凭 delta≤1 数学上不闭合，报告）。  *)
(*   U 形态：U s' = real_inv_pos (real_of_nat |states|) 正性     *)
(*   （对齐根内 bs_minorization 的 Unif = inv_pos nR nR_pos）。  *)
(* ============================================================ *)


(* ---------- 助推：非空有限表势的正性（states_ne 的直用形态） ---------- *)
(* 根内 vocab_len_pos 被无关段变量污染（token_eq_dec/count_token）， *)
(* 此处给出洁净版：Not (Id l nil) ⟹ 0 < of_nat |l|。                *)
Lemma kvev_id_transport : forall (A : Set) (x y : A) (P : A -> Set),
  P x -> Id x y -> P y.
Proof.
  intros A x y P p H. exact (match H with id_refl => p end).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进入提取闭包，   *)
(* 保证 G3 提取 Obj.magic = 0；根内 single_le_sum_aux 的空 match    *)
(* 会产出 2 处 Obj.magic，故不复用）。                              *)
Lemma kvev_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

Lemma kvev_list_len_pos : forall (A : Set) (l : list A),
  Not (Id l nil) -> real_lt real_zero (real_of_nat (length l)).
Proof.
  intros A l. destruct l as [| w rest].
  - intro Hne. exact (match Hne (@id_refl (list A) nil) with end).
  - intro Hne2. cbn [length].
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest)))
             (real_of_nat (Datatypes.S (length rest)))).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* ============================================================ *)
(* Section KVEv：逐出核世界                                       *)
(* ============================================================ *)
Section KVEv.

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states nil).
Variable K : Tok -> Tok -> Real.                       (* 完整行随机核 *)
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').  (* 核逐点正 *)
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* keep 过滤行和：逐出后的失配质量（行归一化的分母） *)
Definition Z_keep (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.

(* 过滤项逐点非负（件 0 与 Z_keep_pos 的共用引理） *)
Lemma Z_keep_entry_nonneg : forall (s y : Tok),
  real_le real_zero (if keep y then K s y else real_zero).
Proof.
  intros s y. destruct (keep y).
  - apply real_le_from_lt_aux. apply Kpos.
  - apply real_le_refl.
Qed.

(* HZk_pos 升级为定理：keep 见证项 K(s,s0) > 0 且 ≤ Z_keep s *)
Theorem Z_keep_pos : forall s : Tok, real_lt real_zero (Z_keep s).
Proof.
  intro s.
  destruct keep_nonempty as [s0 [Hk0 Hin0]].
  assert (Hb : keep s0 = true) by (apply sf_bool_id_true; exact Hk0).
  assert (Hlt0 : real_lt real_zero (if keep s0 then K s s0 else real_zero)).
  { rewrite Hb. apply Kpos. }
  assert (Hle : real_le (if keep s0 then K s s0 else real_zero) (Z_keep s)).
  { apply (kvev_single_le_sum Tok
             (fun y : Tok => if keep y then K s y else real_zero)
             s0 states Hin0).
    intro y. apply Z_keep_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s) Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s)
             Hlt0 Heq).
Qed.

(* 均匀分布 U ≡ 1/|states|（对齐根内 bs_minorization 的 Unif 形态） *)
Definition N_R : Real := real_of_nat (length states).
Theorem N_R_pos : real_lt real_zero N_R.
Proof.
  exact (kvev_list_len_pos Tok states states_ne).
Qed.
Definition U (s' : Tok) : Real := real_inv_pos N_R N_R_pos.

(* δ 与其前提（对齐 AttnDoeblin.v：delta + 上界 + minorization 前提） *)
Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (U s')) (K s s').

(* 逐出核：保留项 K·inv(Z_keep)，逐出项零 *)
Definition K_ev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
  else real_zero.

(* ---------- 件 0：Z_keep s ≤ 1（keep 子和 ≤ 全和 + Krow 桥） ---------- *)
Theorem Z_keep_le_one : forall s : Tok, real_le (Z_keep s) real_one.
Proof.
  intro s.
  apply (real_le_trans _ (real_list_sum Tok (fun s' : Tok => K s s') states)).
  - apply (real_list_sum_le Tok
             (fun s' : Tok => if keep s' then K s s' else real_zero)
             (fun s' : Tok => K s s') states).
    intro y. destruct (keep y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply Kpos.
  - apply (RealSetoid.real_eq_le _ _). apply Krow.
Qed.

(* ---------- 件 1：行归一化 Σ K_ev == 1 ---------- *)
Theorem kev_row_normalized : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K_ev s s') states) real_one.
Proof.
  intro s.
  (* 第一步：逐点改写 K_ev 为 g(s')·inv(Z)，drop 支经 0·x == 0 归零 *)
  apply (real_eq_trans _
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_mult (if keep s' then K s s' else real_zero)
                           (real_inv_pos (Z_keep s) (Z_keep_pos s)))
              states) _).
  { apply (real_list_sum_ext Tok (fun s' : Tok => K_ev s s') _ states).
    intro y. destruct (keep y) eqn:Hk.
    - unfold K_ev. rewrite Hk. apply real_eq_refl.
    - unfold K_ev. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* 第二步：linear_r 提取常数 inv(Z) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) (Z_keep s)) _).
  { apply (real_list_sum_linear_r Tok
             (real_inv_pos (Z_keep s) (Z_keep_pos s))
             (fun s' : Tok => if keep s' then K s s' else real_zero) states). }
  (* 第三步：inv(Z)·Z == 1（comm 桥 + real_inv_pos_correct） *)
  apply (real_eq_trans _
           (real_mult (Z_keep s) (real_inv_pos (Z_keep s) (Z_keep_pos s))) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- 件 2：minorization 传送 δ·U(s') ≤ K_ev s s' ---------- *)
(* 用 kvev_id_transport 沿 Id (keep s') true 投影到 keep 支，        *)
(* 规避 destruct-eqn 对前提的隐式替换。                              *)
Theorem kev_minorization : forall s s' : Tok,
  Id (keep s') true -> real_le (real_mult delta (U s')) (K_ev s s').
Proof.
  intros s s' Hkeep.
  apply (kvev_id_transport bool true (keep s')
           (fun b : bool =>
              real_le (real_mult delta (U s'))
                (if b then
                   real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
                 else real_zero))).
  (* K ≤ K_ev：Z ≤ 1 ⟹ inv(1) ≤ inv(Z)（inv 反单调）⟹ 正乘保序 *)
  - apply (real_le_trans _ (K s s')).
    + apply delta_minor.
    + apply (real_le_trans _
               (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
      * (* K == K·inv(1) 的 eq→le 桥 *)
        apply (RealSetoid.real_eq_le (K s s')
                 (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
        apply real_eq_sym.
        apply (real_eq_trans _ (real_mult (K s s') real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat
                    (K s s') (real_inv_pos real_one real_lt_zero_one)
                    (K s s') real_one).
           ++ apply real_eq_refl.
           ++ apply (real_eq_trans _
                       (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
              ** apply real_eq_sym. apply b4_one_mult.
              ** apply real_inv_pos_correct.
        -- apply real_mult_one.
      * apply (real_le_mult_compat_r (K s s')
                 (real_inv_pos real_one real_lt_zero_one)
                 (real_inv_pos (Z_keep s) (Z_keep_pos s))).
        -- apply real_le_from_lt_aux. apply Kpos.
        -- apply (real_inv_pos_le_compat (Z_keep s) real_one
                    (Z_keep_pos s) real_lt_zero_one).
           apply Z_keep_le_one.
  - exact (id_sym Hkeep).
Qed.

(* ---------- 件 2b：drop 支零形态 + 逐点无条件版 ---------- *)
Theorem kev_drop_zero : forall s s' : Tok,
  Id (keep s') false -> real_eq (K_ev s s') real_zero.
Proof.
  intros s s' Hk.
  apply (kvev_id_transport bool false (keep s')
           (fun b : bool =>
              real_eq (if b then
                         real_mult (K s s')
                           (real_inv_pos (Z_keep s) (Z_keep_pos s))
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hk).
Qed.

Theorem kev_minorization_uncond : forall s s' : Tok,
  real_le (if keep s' then real_mult delta (U s') else real_zero) (K_ev s s').
Proof.
  intros s s'. destruct (keep s') eqn:Hk.
  - apply kev_minorization. apply sf_bool_true_id. exact Hk.
  - apply (RealSetoid.real_eq_le real_zero (K_ev s s')).
    + apply real_eq_sym. apply kev_drop_zero.
      rewrite Hk. apply id_refl.
Qed.

End KVEv.

(* ---------- UpAuditBridge ---------- *)
Module AuditBridge.
(* ============================================================ *)
(* UpAuditBridge：Min-P 截断采样 = 到通过集的 KL 投影（P8 全量）   *)
(* 桥引理 + list-KL 分解恒等式 + 精确代价 + eps 最优性 + hlogz     *)
(* ============================================================ *)
(* 诚实边界（方向纪律）：                                        *)
(*   1) 全部从截断侧度量：KL(q‖full)、KL(q‖minp)、KL(minp‖full)。 *)
(*      不主张 KL(full‖minp)——通过集外 minp 取零点，正性前提不在  *)
(*      手，诚实拒绝该方向。                                     *)
(*   2) Z_aud 语义：= 保留集上【完整核】的质量                    *)
(*      Z_aud = Σ_keep markov_kernel = temp_sum · inv(Z_full)。   *)
(*      这是 KL 投影语义的正确定标（投影基 = 归一化完整核），      *)
(*      故截断代价 KL(minp‖full) = −log Z_aud = log(1/dropped')   *)
(*      即「通过集质量亏损的对数」（kept'=Z_aud, dropped'=1−Z_aud, *)
(*      均以完整核为参照；root 无 real_minp_dropped_mass，故以     *)
(*      kept-mass 形态陈述，见 real_Z_aud_is_kept_mass）。         *)
(*      注意：任务书字面形态「minp == markov_kernel·inv(Σ_keep     *)
(*      temp_factor)」缺 Z_full 定标、代数不闭合；本件按投影语义   *)
(*      修正为「minp == markov_kernel·inv(Z_aud)」，Z_aud 为完整   *)
(*      核的保留质量。                                            *)
(*   3) 根内既有资产直接消费不重证：real_minp_*（RealMinPMain）、  *)
(*      real_list_sum 骨架、real_gibbs/real_kl_term、real_inv_inv、*)
(*      real_log_* 单调族。本文件为 list 世界对接层（根内无此内容）。*)
(*   4) 217 基线：219 .vo 与本机可用 coqc（9.1.0 release，期望     *)
(*      vo 幻数 0x5f91）不兼容（219.vo 幻数 0x5ff4，由另一编译器    *)
(*      产出，9.0/9.1 均拒读），按任务书回退条款 Require          *)
(*      CW214KL_scan（RealMinPMain/KL/求和机器全部在位，行号同源）。 *)
(* ============================================================ *)


Section UpAuditBridge.

(* ---------- Min-P 机器接口（镜像 root RealMinPMain） ---------- *)
Variable Token : Type.
Variable vocab : list Token.
Variable real_temp_factor : Token -> Real.
Variable real_minp_keep : list Token -> Token -> Set.
Variable real_minp_keep_dec : forall (prefix : list Token) (w : Token),
  Or (real_minp_keep prefix w) (Not (real_minp_keep prefix w)).

(* 保留分支项：keep ⟹ temp_factor，drop ⟹ 0
   （定义性 == root real_minp_temp_sum 的求和项） *)
Definition uab_branch (prefix : list Token) (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ => real_temp_factor w
  | inr _ => real_zero
  end.

(* 截断质量 temp_sum := Σ_keep temp_factor（root 机器） *)
Definition uab_temp_sum (prefix : list Token) : Real :=
  real_minp_temp_sum Token vocab real_temp_factor real_minp_keep real_minp_keep_dec prefix.

(* 正性接口（root 诚实接口形态） *)
Variable uab_temp_sum_pos : forall prefix : list Token,
  real_lt real_zero (uab_temp_sum prefix).

(* 诚实接口：温度因子逐 token 正（abstract 层由 exp_neg_pos 提供， *)
(* root RealMinPMain 未假设，KL 项需之，故显式补） *)
Variable uab_temp_factor_pos : forall w : Token, real_lt real_zero (real_temp_factor w).

(* 完整配分（root Real 层无 real_partition_temp——本次补齐） *)
Definition Z_full : Real := real_list_sum Token real_temp_factor vocab.
Variable uab_Z_full_pos : real_lt real_zero Z_full.

(* 完整核（温度化 Boltzmann，root abstract markov_kernel 的 Real 形态） *)
Definition real_markov_kernel (prefix : list Token) (w : Token) : Real :=
  real_mult (real_temp_factor w) (real_inv_pos Z_full uab_Z_full_pos).

(* 审计质量 Z_aud := 完整核的保留质量 == temp_sum · inv(Z_full) *)
Definition Z_aud (prefix : list Token) : Real :=
  real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos).

(* ---------- 透明证书（携带进 real_log 的正性证明项；           *)
(*   必须透明以保 delta/iota 转换一致，禁 Qed 封死） ---------- *)
Definition uab_minp_pos_cert (prefix : list Token) (w : Token) :
  real_lt real_zero (real_mult (real_temp_factor w)
                               (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))) :=
  real_mult_positive (real_temp_factor w)
                     (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                     (uab_temp_factor_pos w) (real_inv_pos_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix)).

Definition uab_full_pos_cert (prefix : list Token) (w : Token) :
  real_lt real_zero (real_markov_kernel prefix w) :=
  real_mult_positive (real_temp_factor w) (real_inv_pos Z_full uab_Z_full_pos)
                     (uab_temp_factor_pos w) (real_inv_pos_pos Z_full uab_Z_full_pos).

Definition uab_Z_aud_pos_cert (prefix : list Token) :
  real_lt real_zero (Z_aud prefix) :=
  real_mult_positive (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos)
                     (uab_temp_sum_pos prefix) (real_inv_pos_pos Z_full uab_Z_full_pos).

(* min-p 核（root real_minp_markov_kernel 的本地摘要） *)
Definition uab_minp_kernel (prefix : list Token) (w : Token) : Real :=
  real_minp_markov_kernel Token vocab real_temp_factor real_minp_keep real_minp_keep_dec
                          uab_temp_sum_pos prefix w.

(* min-p 核 keep 支正性（透明 Defined：keep 支即 uab_minp_pos_cert，
   delta+iota 后与证书项转换一致——不得 Qed 封死） *)
Definition uab_minp_keep_pos (prefix : list Token) (w : Token)
  (Hk : real_minp_keep prefix w) : real_lt real_zero (uab_minp_kernel prefix w).
Proof.
  unfold uab_minp_kernel, real_minp_markov_kernel.
  destruct (real_minp_keep_dec prefix w) as [Hk' | Hd].
  - exact (uab_minp_pos_cert prefix w).
  - destruct (Hd Hk).
Defined.

(* min-p 核 drop 支恒零（Hq_fail 形态；不进 log 证书，可 Qed） *)
Lemma uab_minp_fail_zero : forall (prefix : list Token) (w : Token),
  Not (real_minp_keep prefix w) -> real_eq (uab_minp_kernel prefix w) real_zero.
Proof.
  intros prefix w Hd. unfold uab_minp_kernel, real_minp_markov_kernel.
  destruct (real_minp_keep_dec prefix w) as [Hk | Hd'].
  - destruct (Hd Hk).
  - apply real_eq_refl.
Qed.

(* ---------- 基础代数（real_eq 层小工具） ---------- *)

Lemma uab_one_mult : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

Lemma uab_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

Lemma uab_plus_zero_opp : forall a : Real, real_eq (real_plus (real_opp a) a) real_zero.
Proof.
  intro a. apply (real_eq_trans _ (real_plus a (real_opp a)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

Lemma uab_list_sum_zero : forall (X : Type) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l. induction l as [| w rest IH]; simpl.
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_list_sum X (fun _ : X => real_zero) rest) _).
    + apply uab_plus_zero_l.
    + exact IH.
Qed.

(* 逆的唯一性：x·y == 1 ⟹ y == inv(x)（由 inv_pos_correct + 环代数） *)
Lemma uab_inv_unique : forall (x y : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x y) real_one -> real_eq y (real_inv_pos x Hx).
Proof.
  intros x y Hx Hxy.
  apply (real_eq_trans _ (real_mult real_one y) _).
  - apply (real_eq_sym _ _ (uab_one_mult y)).
  - apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos x Hx) x) y) _).
    + apply (RealSetoid.real_eq_mult_compat real_one y
               (real_mult (real_inv_pos x Hx) x) y
               (real_eq_sym (real_mult (real_inv_pos x Hx) x) real_one
                 (real_eq_trans (real_mult (real_inv_pos x Hx) x)
                                (real_mult x (real_inv_pos x Hx)) real_one
                                (real_mult_comm (real_inv_pos x Hx) x)
                                (real_inv_pos_correct x Hx)))
               (real_eq_refl y)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) (real_mult x y)) _).
      * apply (real_eq_sym _ _ (real_mult_assoc (real_inv_pos x Hx) x y)).
      * apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx) (real_mult x y)
                    (real_inv_pos x Hx) real_one (real_eq_refl _) Hxy).
        -- apply real_mult_one.
Qed.

(* 逆元对乘法的分配：inv(a·b) == inv(a)·inv(b)（root L95695 abstract 版 *)
(* 的 Real 层本地复刻；root 该引理在 217 基线快照之外） *)
Lemma uab_inv_mult_distr : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb))
          (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)).
Proof.
  intros a b Ha Hb.
  apply (real_eq_sym (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                     (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb))).
  apply (uab_inv_unique (real_mult a b) (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                        (real_mult_positive a b Ha Hb)).
  (* 目标：(a·b)·(Ja·Jb) == one *)
  assert (K1 : real_eq (real_mult (real_inv_pos b Hb) (real_mult a b))
                       (real_mult a real_one)).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos b Hb) a) b) _).
    - apply real_mult_assoc.
    - apply (real_eq_trans _ (real_mult (real_mult a (real_inv_pos b Hb)) b) _).
      + apply (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos b Hb) a)
                 b (real_mult a (real_inv_pos b Hb)) b
                 (real_mult_comm (real_inv_pos b Hb) a) (real_eq_refl b)).
      + apply (real_eq_trans _ (real_mult a (real_mult (real_inv_pos b Hb) b)) _).
        * apply (real_eq_sym _ _ (real_mult_assoc a (real_inv_pos b Hb) b)).
        * apply (RealSetoid.real_eq_mult_compat a (real_mult (real_inv_pos b Hb) b)
                   a real_one (real_eq_refl a)
                   (real_eq_trans (real_mult (real_inv_pos b Hb) b)
                                  (real_mult b (real_inv_pos b Hb)) real_one
                                  (real_mult_comm (real_inv_pos b Hb) b)
                                  (real_inv_pos_correct b Hb))). }
  apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                                    (real_mult a b)) _).
  - apply real_mult_comm.
  - apply (real_eq_trans _ (real_mult (real_inv_pos a Ha)
                                      (real_mult (real_inv_pos b Hb) (real_mult a b))) _).
    + apply (real_eq_sym _ _ (real_mult_assoc (real_inv_pos a Ha) (real_inv_pos b Hb)
                                 (real_mult a b))).
    + apply (real_eq_trans _ (real_mult (real_inv_pos a Ha) (real_mult a real_one)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha)
                 (real_mult (real_inv_pos b Hb) (real_mult a b))
                 (real_inv_pos a Ha) (real_mult a real_one)
                 (real_eq_refl _) K1).
      * apply (real_eq_trans _ (real_mult (real_inv_pos a Ha) a) _).
        -- apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha)
                     (real_mult a real_one) (real_inv_pos a Ha) a
                     (real_eq_refl _) (real_mult_one a)).
        -- apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha)) _).
           ++ apply real_mult_comm.
           ++ apply (real_inv_pos_correct a Ha).
Qed.

(* ---------- log 代数 ---------- *)

(* log(inv x) == −log x（由 log(x·inv x) == log 1 == 0 + 加法整理） *)
Lemma uab_log_inv_neg : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hsum : real_eq (real_plus (real_log x Hx)
                                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                         real_zero).
  { apply (real_eq_trans _ (real_log (real_mult x (real_inv_pos x Hx))
                                     (real_mult_positive x (real_inv_pos x Hx) Hx
                                       (real_inv_pos_pos x Hx))) _).
    - apply (real_eq_sym _ _ (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    - apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      + apply (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                 (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))
                 real_lt_zero_one (real_inv_pos_correct x Hx)).
      + apply (real_log_one real_lt_zero_one). }
  assert (Hdir : real_eq (real_opp (real_log x Hx))
                         (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  { apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    - apply (real_eq_sym _ _ (real_plus_zero (real_opp (real_log x Hx)))).
    - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx))
                                        (real_plus (real_log x Hx)
                                                   (real_log (real_inv_pos x Hx)
                                                             (real_inv_pos_pos x Hx)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log x Hx)) real_zero
                 (real_opp (real_log x Hx))
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 (real_eq_refl _)
                 (real_eq_sym (real_plus (real_log x Hx)
                                         (real_log (real_inv_pos x Hx)
                                                   (real_inv_pos_pos x Hx)))
                              real_zero Hsum)).
      + apply (real_eq_trans _
                 (real_plus (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
        * apply (real_plus_assoc (real_opp (real_log x Hx)) (real_log x Hx)
                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
        * apply (real_eq_trans _ (real_plus real_zero
                                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
          -- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                       (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       real_zero (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       (uab_plus_zero_opp (real_log x Hx)) (real_eq_refl _)).
          -- apply uab_plus_zero_l. }
  apply (real_eq_sym _ _ Hdir).
Qed.

(* 加法尺度拆分：(L + −p) + −(L + −q) == −(p + −q)（A1） *)
Lemma uab_add_scale_split : forall (L p q : Real),
  real_eq (real_plus (real_plus L (real_opp p)) (real_opp (real_plus L (real_opp q))))
          (real_opp (real_plus p (real_opp q))).
Proof.
  intros L p q.
  (* S1 : −(L + −q) == −L + q *)
  assert (S1 : real_eq (real_opp (real_plus L (real_opp q)))
                       (real_plus (real_opp L) q)).
  { apply (real_eq_trans _ (real_plus (real_opp L) (real_opp (real_opp q))) _).
    - apply (real_opp_plus L (real_opp q)).
    - apply (RealSetoid.real_eq_plus_compat (real_opp L) (real_opp (real_opp q))
               (real_opp L) q (real_eq_refl _) (real_opp_opp q)). }
  (* S2 : (−p + (−L + q)) == ((−L + −p) + q) *)
  assert (S2 : real_eq (real_plus (real_opp p) (real_plus (real_opp L) q))
                       (real_plus (real_plus (real_opp L) (real_opp p)) q)).
  { apply (real_eq_trans _ (real_plus (real_plus (real_opp p) (real_opp L)) q) _).
    - apply (real_plus_assoc (real_opp p) (real_opp L) q).
    - apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp p) (real_opp L))
               q (real_plus (real_opp L) (real_opp p)) q
               (real_plus_comm (real_opp p) (real_opp L)) (real_eq_refl q)). }
  (* S3 : L + (−L + −p) == (L + −L) + −p *)
  assert (S3 : real_eq (real_plus L (real_plus (real_opp L) (real_opp p)))
                       (real_plus (real_plus L (real_opp L)) (real_opp p))).
  { apply (real_plus_assoc L (real_opp L) (real_opp p)). }
  (* S4 : (L + −L) + −p == zero + −p == −p *)
  assert (S4 : real_eq (real_plus (real_plus L (real_opp L)) (real_opp p))
                       (real_opp p)).
  { apply (real_eq_trans _ (real_plus real_zero (real_opp p)) _).
    - apply (RealSetoid.real_eq_plus_compat (real_plus L (real_opp L)) (real_opp p)
               real_zero (real_opp p) (real_plus_opp L) (real_eq_refl _)).
    - apply uab_plus_zero_l. }
  (* S5 : −p + q == −(p + −q) *)
  assert (S5 : real_eq (real_plus (real_opp p) q)
                       (real_opp (real_plus p (real_opp q)))).
  { apply (real_eq_trans _ (real_plus (real_opp p) (real_opp (real_opp q))) _).
    - apply (RealSetoid.real_eq_plus_compat (real_opp p) q (real_opp p)
               (real_opp (real_opp q)) (real_eq_refl _)
               (real_eq_sym _ _ (real_opp_opp q))).
    - apply (real_eq_sym _ _ (real_opp_plus p (real_opp q))). }
  apply (real_eq_trans _ (real_plus (real_plus L (real_opp p))
                                    (real_plus (real_opp L) q)) _).
  - apply (RealSetoid.real_eq_plus_compat (real_plus L (real_opp p))
             (real_opp (real_plus L (real_opp q)))
             (real_plus L (real_opp p)) (real_plus (real_opp L) q)
             (real_eq_refl _) S1).
  - apply (real_eq_trans _ (real_plus L (real_plus (real_opp p) (real_plus (real_opp L) q))) _).
    + apply (real_eq_sym _ _ (real_plus_assoc L (real_opp p) (real_plus (real_opp L) q))).
    + apply (real_eq_trans _ (real_plus L (real_plus (real_plus (real_opp L) (real_opp p)) q)) _).
      * apply (RealSetoid.real_eq_plus_compat L
                 (real_plus (real_opp p) (real_plus (real_opp L) q))
                 L (real_plus (real_plus (real_opp L) (real_opp p)) q)
                 (real_eq_refl _) S2).
      * apply (real_eq_trans _
                 (real_plus (real_plus L (real_plus (real_opp L) (real_opp p))) q) _).
        -- apply (real_plus_assoc L (real_plus (real_opp L) (real_opp p)) q).
        -- apply (real_eq_trans _
                    (real_plus (real_plus (real_plus L (real_opp L)) (real_opp p)) q) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus L (real_plus (real_opp L) (real_opp p)))
                       q (real_plus (real_plus L (real_opp L)) (real_opp p)) q
                       S3 (real_eq_refl q)).
           ++ apply (real_eq_trans _ (real_plus (real_plus real_zero (real_opp p)) q) _).
              ** apply (RealSetoid.real_eq_plus_compat
                          (real_plus (real_plus L (real_opp L)) (real_opp p))
                          q (real_plus real_zero (real_opp p)) q
                          (RealSetoid.real_eq_plus_compat (real_plus L (real_opp L))
                             (real_opp p) real_zero (real_opp p)
                             (real_plus_opp L) (real_eq_refl _))
                          (real_eq_refl q)).
              ** apply (real_eq_trans _ (real_plus (real_opp p) q) _).
                 --- apply (RealSetoid.real_eq_plus_compat (real_plus real_zero (real_opp p))
                              q (real_opp p) q (uab_plus_zero_l (real_opp p))
                              (real_eq_refl q)).
                 --- apply S5.
Qed.

(* 逐点核心（P3）：log(minp形态) − log(full形态) == −log Z_aud
   （无分支形态：对 inline 乘积陈述，证书全透明一致） *)
(* Z_aud 与其展开形的 log 转换桥（apply 统一器不展开 Section 内定义，
   以 exact 的完整转换检查显式过桥） *)
Lemma uab_Z_aud_log_bridge : forall prefix : list Token,
  real_eq (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))
          (real_log (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
                    (uab_Z_aud_pos_cert prefix)).
Proof.
  intro prefix. exact (real_eq_refl _).
Qed.

Lemma uab_log_minp_minus_full : forall (prefix : list Token) (w : Token),
  real_eq (real_plus (real_log (real_mult (real_temp_factor w)
                                          (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix)))
                               (uab_minp_pos_cert prefix w))
                     (real_opp (real_log (real_mult (real_temp_factor w)
                                                    (real_inv_pos Z_full uab_Z_full_pos))
                                         (uab_full_pos_cert prefix w))))
          (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intros prefix w.
  assert (Hm : real_eq (real_log (real_mult (real_temp_factor w)
                                            (real_inv_pos (uab_temp_sum prefix)
                                                          (uab_temp_sum_pos prefix)))
                                 (uab_minp_pos_cert prefix w))
                       (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                                  (real_opp (real_log (uab_temp_sum prefix)
                                                      (uab_temp_sum_pos prefix))))).
  { apply (real_eq_trans _
             (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                        (real_log (real_inv_pos (uab_temp_sum prefix)
                                                (uab_temp_sum_pos prefix))
                                  (real_inv_pos_pos (uab_temp_sum prefix)
                                                    (uab_temp_sum_pos prefix)))) _).
    - apply (real_log_mult (real_temp_factor w)
                           (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                           (uab_temp_factor_pos w)
                           (real_inv_pos_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))).
    - apply (RealSetoid.real_eq_plus_compat
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_log (real_inv_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                         (real_inv_pos_pos (uab_temp_sum prefix) (uab_temp_sum_pos prefix)))
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_opp (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix)))
               (real_eq_refl _)
               (uab_log_inv_neg (uab_temp_sum prefix) (uab_temp_sum_pos prefix))). }
  assert (Hf : real_eq (real_log (real_mult (real_temp_factor w)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                                 (uab_full_pos_cert prefix w))
                       (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                                  (real_opp (real_log Z_full uab_Z_full_pos)))).
  { apply (real_eq_trans _
             (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                        (real_log (real_inv_pos Z_full uab_Z_full_pos)
                                  (real_inv_pos_pos Z_full uab_Z_full_pos))) _).
    - apply (real_log_mult (real_temp_factor w) (real_inv_pos Z_full uab_Z_full_pos)
                           (uab_temp_factor_pos w) (real_inv_pos_pos Z_full uab_Z_full_pos)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_log (real_inv_pos Z_full uab_Z_full_pos)
                         (real_inv_pos_pos Z_full uab_Z_full_pos))
               (real_log (real_temp_factor w) (uab_temp_factor_pos w))
               (real_opp (real_log Z_full uab_Z_full_pos))
               (real_eq_refl _) (uab_log_inv_neg Z_full uab_Z_full_pos)). }
  assert (Hz : real_eq (real_log (real_mult (uab_temp_sum prefix)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                                 (uab_Z_aud_pos_cert prefix))
                       (real_plus (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                                  (real_opp (real_log Z_full uab_Z_full_pos)))).
  { apply (real_eq_trans _
             (real_log (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
                       (real_mult_positive (uab_temp_sum prefix)
                                           (real_inv_pos Z_full uab_Z_full_pos)
                                           (uab_temp_sum_pos prefix)
                                           (real_inv_pos_pos Z_full uab_Z_full_pos))) _).
    - apply (real_log_wd
               (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
               (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
               (uab_Z_aud_pos_cert prefix)
               (real_mult_positive (uab_temp_sum prefix)
                                   (real_inv_pos Z_full uab_Z_full_pos)
                                   (uab_temp_sum_pos prefix)
                                   (real_inv_pos_pos Z_full uab_Z_full_pos))
               (real_eq_refl _)).
    - apply (real_eq_trans _
               (real_plus (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                          (real_log (real_inv_pos Z_full uab_Z_full_pos)
                                    (real_inv_pos_pos Z_full uab_Z_full_pos))) _).
      + apply (real_log_mult (uab_temp_sum prefix)
                             (real_inv_pos Z_full uab_Z_full_pos)
                             (uab_temp_sum_pos prefix)
                             (real_inv_pos_pos Z_full uab_Z_full_pos)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                 (real_log (real_inv_pos Z_full uab_Z_full_pos)
                           (real_inv_pos_pos Z_full uab_Z_full_pos))
                 (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                 (real_opp (real_log Z_full uab_Z_full_pos))
                 (real_eq_refl _)
                 (uab_log_inv_neg Z_full uab_Z_full_pos)). }
  apply (real_eq_trans _
           (real_plus (real_plus (real_log (real_temp_factor w) (uab_temp_factor_pos w))
                                 (real_opp (real_log (uab_temp_sum prefix)
                                                     (uab_temp_sum_pos prefix))))
                      (real_opp (real_plus (real_log (real_temp_factor w)
                                                           (uab_temp_factor_pos w))
                                           (real_opp (real_log Z_full uab_Z_full_pos))))) _).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ Hm
             (RealSetoid.real_eq_opp_compat _ _ Hf)).
  - apply (real_eq_trans _
             (real_opp (real_plus (real_log (uab_temp_sum prefix) (uab_temp_sum_pos prefix))
                                  (real_opp (real_log Z_full uab_Z_full_pos)))) _).
    + apply uab_add_scale_split.
    + apply (RealSetoid.real_eq_opp_compat _ _).
      * apply (real_eq_sym _ _ Hz).
Qed.

(* 尺度恒等式（件 1 keep 支核心代数，单引理封装）：
   x·inv(a) == (x·inv(b))·inv(a·inv(b))
   经 inv_pos_mult_distr + real_inv_inv + real_inv_pos_correct + 环代数 *)
Lemma uab_scale_identity : forall (x a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_mult x (real_inv_pos a Ha))
          (real_mult (real_mult x (real_inv_pos b Hb))
                     (real_inv_pos (real_mult a (real_inv_pos b Hb))
                                   (real_mult_positive a (real_inv_pos b Hb) Ha
                                     (real_inv_pos_pos b Hb)))).
Proof.
  intros x a b Ha Hb.
  assert (S1 : real_eq (real_inv_pos (real_mult a (real_inv_pos b Hb))
                                     (real_mult_positive a (real_inv_pos b Hb) Ha
                                       (real_inv_pos_pos b Hb)))
                       (real_mult (real_inv_pos a Ha) b)).
  { apply (real_eq_trans _
             (real_mult (real_inv_pos a Ha)
                        (real_inv_pos (real_inv_pos b Hb) (real_inv_pos_pos b Hb))) _).
    - apply (uab_inv_mult_distr a (real_inv_pos b Hb) Ha (real_inv_pos_pos b Hb)).
    - apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha)
               (real_inv_pos (real_inv_pos b Hb) (real_inv_pos_pos b Hb))
               (real_inv_pos a Ha) b (real_eq_refl _)
               (real_inv_inv b Hb (real_inv_pos_pos b Hb))). }
  (* 正向链：x·Ja == x·(Ja·one) == x·(Ja·(Jb·b)) == ... == (x·Jb)·inv(a·Jb) *)
  apply (real_eq_trans _ (real_mult x (real_mult (real_inv_pos a Ha) real_one)) _).
  - apply (RealSetoid.real_eq_mult_compat x (real_inv_pos a Ha)
             x (real_mult (real_inv_pos a Ha) real_one)
             (real_eq_refl x) (real_eq_sym _ _ (real_mult_one (real_inv_pos a Ha)))).
  - apply (real_eq_trans _
             (real_mult x (real_mult (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b))) _).
    + apply (RealSetoid.real_eq_mult_compat x (real_mult (real_inv_pos a Ha) real_one)
               x (real_mult (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b))
               (real_eq_refl x)
               (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) real_one
                  (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b)
                  (real_eq_refl _)
                  (real_eq_sym _ _
                    (real_eq_trans (real_mult (real_inv_pos b Hb) b)
                                   (real_mult b (real_inv_pos b Hb)) real_one
                                   (real_mult_comm (real_inv_pos b Hb) b)
                                   (real_inv_pos_correct b Hb))))).
    + apply (real_eq_trans _
               (real_mult x (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) b)) _).
      * apply (RealSetoid.real_eq_mult_compat x
                 (real_mult (real_inv_pos a Ha) (real_mult (real_inv_pos b Hb) b))
                 x (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) b)
                 (real_eq_refl x) (real_mult_assoc (real_inv_pos a Ha) (real_inv_pos b Hb) b)).
      * apply (real_eq_trans _
                 (real_mult x (real_mult (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b)) _).
        -- apply (RealSetoid.real_eq_mult_compat x
                    (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)) b)
                    x (real_mult (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b)
                    (real_eq_refl x)
                    (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos a Ha)
                                                        (real_inv_pos b Hb))
                       b (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b
                       (real_mult_comm (real_inv_pos a Ha) (real_inv_pos b Hb))
                       (real_eq_refl b))).
        -- apply (real_eq_trans _
                     (real_mult x (real_mult (real_inv_pos b Hb) (real_mult (real_inv_pos a Ha) b))) _).
           ++ apply (RealSetoid.real_eq_mult_compat x
                       (real_mult (real_mult (real_inv_pos b Hb) (real_inv_pos a Ha)) b)
                       x (real_mult (real_inv_pos b Hb) (real_mult (real_inv_pos a Ha) b))
                       (real_eq_refl x)
                       (real_eq_sym _ _ (real_mult_assoc (real_inv_pos b Hb)
                                                          (real_inv_pos a Ha) b))).
           ++ apply (real_eq_trans _
                       (real_mult (real_mult x (real_inv_pos b Hb)) (real_mult (real_inv_pos a Ha) b)) _).
              ** apply (real_mult_assoc x (real_inv_pos b Hb) (real_mult (real_inv_pos a Ha) b)).
              ** apply (RealSetoid.real_eq_mult_compat
                          (real_mult x (real_inv_pos b Hb)) (real_mult (real_inv_pos a Ha) b)
                          (real_mult x (real_inv_pos b Hb))
                          (real_inv_pos (real_mult a (real_inv_pos b Hb))
                                        (real_mult_positive a (real_inv_pos b Hb) Ha
                                          (real_inv_pos_pos b Hb)))
                          (real_eq_refl _) (real_eq_sym _ _ S1)).
Qed.

(* ============================================================ *)
(* 件 1（桥引理）：min-p 核 == 投影形态                          *)
(*   keep 支：minp w == markov_kernel w · inv(Z_aud)             *)
(*   drop 支：两侧皆零                                           *)
(* ============================================================ *)

Definition uab_proj_kernel (prefix : list Token) (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ => real_mult (real_markov_kernel prefix w)
                       (real_inv_pos (Z_aud prefix) (uab_Z_aud_pos_cert prefix))
  | inr _ => real_zero
  end.

Theorem real_minp_kernel_is_projection : forall (prefix : list Token) (w : Token),
  real_eq (uab_minp_kernel prefix w) (uab_proj_kernel prefix w).
Proof.
  intros prefix w.
  unfold uab_minp_kernel, real_minp_markov_kernel, uab_proj_kernel.
  destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
  - (* keep 支：尺度恒等式（Z_aud delta 展开 == S·inv(Z_full)） *)
    apply (uab_scale_identity (real_temp_factor w) (uab_temp_sum prefix) Z_full
             (uab_temp_sum_pos prefix) uab_Z_full_pos).
  - (* drop 支：两侧皆零 *)
    apply real_eq_refl.
Qed.

(* temp_sum 与其 list 展开形的转换桥（exact 全转换，绕 apply 统一器限制） *)
Lemma uab_temp_sum_list_bridge : forall prefix : list Token,
  real_eq (real_list_sum Token (uab_branch prefix) vocab) (uab_temp_sum prefix).
Proof. intro prefix. exact (real_eq_refl _). Qed.

(* ============================================================ *)
(* 件 1b：Z_aud == 保留集上完整核质量；投影形态核归一化           *)
(* ============================================================ *)

Theorem real_Z_aud_is_kept_mass : forall prefix : list Token,
  real_eq (Z_aud prefix)
          (real_list_sum Token
             (fun w : Token =>
                match real_minp_keep_dec prefix w with
                | inl _ => real_markov_kernel prefix w
                | inr _ => real_zero
                end) vocab).
Proof.
  intro prefix. unfold Z_aud.
  assert (Hfwd : real_eq (real_list_sum Token
                            (fun w : Token =>
                               match real_minp_keep_dec prefix w with
                               | inl _ => real_markov_kernel prefix w
                               | inr _ => real_zero
                               end) vocab)
                         (real_mult (uab_temp_sum prefix)
                                    (real_inv_pos Z_full uab_Z_full_pos))).
  { apply (real_eq_trans _
             (real_list_sum Token
                (fun w : Token => real_mult (uab_branch prefix w)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                vocab) _).
    - apply (real_list_sum_ext Token
                (fun w : Token =>
                   match real_minp_keep_dec prefix w with
                   | inl _ => real_markov_kernel prefix w
                   | inr _ => real_zero
                   end)
                (fun w : Token => real_mult (uab_branch prefix w)
                                            (real_inv_pos Z_full uab_Z_full_pos))
                vocab).
      intro w. destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
      + unfold real_markov_kernel, uab_branch.
        destruct (real_minp_keep_dec prefix w) as [Hk2 | Hd2].
        * apply real_eq_refl.
        * destruct (Hd2 Hk).
      + unfold uab_branch.
        destruct (real_minp_keep_dec prefix w) as [Hk2 | Hd2].
        * destruct (Hd Hk2).
        * apply (real_eq_sym _ _
                   (real_eq_trans (real_mult real_zero (real_inv_pos Z_full uab_Z_full_pos))
                                  (real_mult (real_inv_pos Z_full uab_Z_full_pos) real_zero)
                                  real_zero
                                  (real_mult_comm real_zero (real_inv_pos Z_full uab_Z_full_pos))
                                  (real_mult_zero (real_inv_pos Z_full uab_Z_full_pos)))).
    - apply (real_eq_trans _
                (real_mult (real_inv_pos Z_full uab_Z_full_pos)
                           (real_list_sum Token (uab_branch prefix) vocab)) _).
      + apply (real_list_sum_linear_r Token (real_inv_pos Z_full uab_Z_full_pos)
                    (uab_branch prefix) vocab).
      + apply (real_eq_trans _
                  (real_mult (real_inv_pos Z_full uab_Z_full_pos) (uab_temp_sum prefix)) _).
        * apply (RealSetoid.real_eq_mult_compat (real_inv_pos Z_full uab_Z_full_pos)
                    (real_list_sum Token (uab_branch prefix) vocab)
                    (real_inv_pos Z_full uab_Z_full_pos) (uab_temp_sum prefix)
                    (real_eq_refl _) (uab_temp_sum_list_bridge prefix)).
        * apply real_mult_comm. }
  exact (real_eq_sym _ _ Hfwd).
Qed.

Theorem real_proj_normalized_list : forall prefix : list Token,
  real_eq (real_list_sum Token (uab_proj_kernel prefix) vocab) real_one.
Proof.
  intro prefix.
  apply (real_eq_trans _ (real_list_sum Token (uab_minp_kernel prefix) vocab) _).
  - apply (real_list_sum_ext Token (uab_proj_kernel prefix) (uab_minp_kernel prefix) vocab).
    intro w. apply (real_eq_sym _ _ (real_minp_kernel_is_projection prefix w)).
  - exact (real_minp_markov_kernel_normalized Token vocab real_temp_factor
             real_minp_keep real_minp_keep_dec uab_temp_sum_pos prefix).
Qed.

(* ============================================================ *)
(* 件 5（hlogz 接入）：Z_aud ≤ 1 ⟹ log Z_aud ≤ 0 ⟹ 代价项非负    *)
(* ============================================================ *)

Theorem real_Z_aud_le_one : forall prefix : list Token,
  real_le (Z_aud prefix) real_one.
Proof.
  intro prefix.
  assert (Hpt : forall w : Token,
             real_le (match real_minp_keep_dec prefix w with
                      | inl _ => real_temp_factor w
                      | inr _ => real_zero
                      end) (real_temp_factor w)).
  { intro w. destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    - apply real_le_refl.
    - apply (RealSetoid.real_lt_le_iff_req real_zero (real_temp_factor w)).
      exact (inl (uab_temp_factor_pos w)). }
  assert (Hsum : real_le (uab_temp_sum prefix) Z_full).
  { unfold uab_temp_sum, real_minp_temp_sum, Z_full.
    apply (real_list_sum_le Token
             (fun w : Token =>
                match real_minp_keep_dec prefix w with
                | inl _ => real_temp_factor w
                | inr _ => real_zero
                end) real_temp_factor vocab Hpt). }
  unfold Z_aud.
  apply (RealSetoid.real_le_id_r
           (real_mult (uab_temp_sum prefix) (real_inv_pos Z_full uab_Z_full_pos))
           (real_mult Z_full (real_inv_pos Z_full uab_Z_full_pos)) real_one
           (real_inv_pos_correct Z_full uab_Z_full_pos)).
  apply (real_le_mult_compat (uab_temp_sum prefix) Z_full
           (real_inv_pos Z_full uab_Z_full_pos)
           (real_inv_pos_pos Z_full uab_Z_full_pos) Hsum).
Qed.

Theorem real_log_Z_aud_le_zero : forall prefix : list Token,
  real_le (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)) real_zero.
Proof.
  intro prefix.
  pose proof (real_Z_aud_le_one prefix) as HZ1.
  unfold real_le in HZ1. destruct HZ1 as [Hlt | Heq].
  - apply (RealSetoid.real_le_id_r (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))
             (real_log real_one real_lt_zero_one) real_zero (real_log_one real_lt_zero_one)).
    apply (RealSetoid.real_lt_le_iff_req (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))
             (real_log real_one real_lt_zero_one)).
    exact (inl (real_log_lt_mono (Z_aud prefix) real_one
                  (uab_Z_aud_pos_cert prefix) real_lt_zero_one Hlt)).
  - apply (RealSetoid.real_eq_le (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)) real_zero).
    apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    + apply (real_log_wd (Z_aud prefix) real_one
               (uab_Z_aud_pos_cert prefix) real_lt_zero_one Heq).
    + apply (real_log_one real_lt_zero_one).
Qed.

Theorem real_opp_log_Z_aud_nonneg : forall prefix : list Token,
  real_le real_zero (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intro prefix.
  apply (RealSetoid.real_le_id_l real_zero (real_opp real_zero)
           (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
           (real_eq_sym real_zero (real_opp real_zero) real_opp_zero)).
  apply (real_opp_le_compat (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)) real_zero).
  exact (real_log_Z_aud_le_zero prefix).
Qed.

(* ============================================================ *)
(* 件 2：list-KL 分解恒等式（kl_sum_split / kl_tail_eval 骨架的   *)
(*       list Token 世界复刻）                                   *)
(*   求和项按 keep_dec 分支；drop 支两侧归零；证书全透明          *)
(* ============================================================ *)

(* KL 求和项（q 对完整核） *)
Definition uab_kl_q_full (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl Hk =>
      real_mult (q w)
        (real_plus (real_log (q w) (Hq w Hk))
                   (real_opp (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos Z_full uab_Z_full_pos))
                                       (uab_full_pos_cert prefix w))))
  | inr _ => real_zero
  end.

(* KL 求和项（q 对 min-p 核 keep 支形态） *)
Definition uab_kl_q_minp (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl Hk =>
      real_mult (q w)
        (real_plus (real_log (q w) (Hq w Hk))
                   (real_opp (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos (uab_temp_sum prefix)
                                                                (uab_temp_sum_pos prefix)))
                                       (uab_minp_pos_cert prefix w))))
  | inr _ => real_zero
  end.

(* 尾项求和项（q·(log minp − log full)） *)
Definition uab_kl_tail (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (w : Token) : Real :=
  match real_minp_keep_dec prefix w with
  | inl _ =>
      real_mult (q w)
        (real_plus (real_log (real_mult (real_temp_factor w)
                                        (real_inv_pos (uab_temp_sum prefix)
                                                      (uab_temp_sum_pos prefix)))
                             (uab_minp_pos_cert prefix w))
                   (real_opp (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos Z_full uab_Z_full_pos))
                                       (uab_full_pos_cert prefix w))))
  | inr _ => real_zero
  end.

(* a − c == (a − b) + (b − c)（real_eq 形态，root kl_minus_split 的 list 版） *)
Lemma uab_minus_split : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c)))) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_opp c) a
             (real_plus (real_opp b) (real_plus b (real_opp c)))
             (real_eq_refl a)
             (real_eq_sym _ _
               (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c)))
                              (real_plus (real_plus (real_opp b) b) (real_opp c))
                              (real_opp c)
                              (real_plus_assoc (real_opp b) b (real_opp c))
                              (real_eq_trans
                                 (real_plus (real_plus (real_opp b) b) (real_opp c))
                                 (real_plus real_zero (real_opp c))
                                 (real_opp c)
                                 (RealSetoid.real_eq_plus_compat
                                    (real_plus (real_opp b) b) (real_opp c)
                                    real_zero (real_opp c)
                                    (uab_plus_zero_opp b) (real_eq_refl _))
                                 (uab_plus_zero_l (real_opp c)))))).
  - apply (real_plus_assoc a (real_opp b) (real_plus b (real_opp c))).
Qed.

(* 逐点分解：q·(log q − log full) == q·(log q − log minp) + q·(log minp − log full) *)
Lemma uab_kl_pointwise_split : forall (prefix : list Token) (q : Token -> Real)
  (Hq : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w)) (w : Token),
  real_eq (uab_kl_q_full prefix q Hq w)
          (real_plus (uab_kl_q_minp prefix q Hq w) (uab_kl_tail prefix q Hq w)).
Proof.
  intros prefix q Hq w.
  unfold uab_kl_q_full, uab_kl_q_minp, uab_kl_tail.
  destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
  - (* q·(L − F) == q·((L − M) + (M − F)) == q·(L − M) + q·(M − F) *)
    apply (real_eq_trans _
             (real_mult (q w)
                (real_plus (real_plus (real_log (q w) (Hq w Hk))
                                      (real_opp (real_log (real_mult (real_temp_factor w)
                                                                      (real_inv_pos (uab_temp_sum prefix)
                                                                                       (uab_temp_sum_pos prefix)))
                                                          (uab_minp_pos_cert prefix w))))
                           (real_plus (real_log (real_mult (real_temp_factor w)
                                                           (real_inv_pos (uab_temp_sum prefix)
                                                                         (uab_temp_sum_pos prefix)))
                                                (uab_minp_pos_cert prefix w))
                                      (real_opp (real_log (real_mult (real_temp_factor w)
                                                                      (real_inv_pos Z_full
                                                                                       uab_Z_full_pos))
                                                           (uab_full_pos_cert prefix w)))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q w)
               (real_plus (real_log (q w) (Hq w Hk))
                          (real_opp (real_log (real_mult (real_temp_factor w)
                                                          (real_inv_pos Z_full uab_Z_full_pos))
                                       (uab_full_pos_cert prefix w))))
               (q w)
               (real_plus (real_plus (real_log (q w) (Hq w Hk))
                                     (real_opp (real_log (real_mult (real_temp_factor w)
                                                                     (real_inv_pos (uab_temp_sum prefix)
                                                                                   (uab_temp_sum_pos prefix)))
                                                         (uab_minp_pos_cert prefix w))))
                          (real_plus (real_log (real_mult (real_temp_factor w)
                                                          (real_inv_pos (uab_temp_sum prefix)
                                                                        (uab_temp_sum_pos prefix)))
                                                       (uab_minp_pos_cert prefix w))
                                     (real_opp (real_log (real_mult (real_temp_factor w)
                                                                     (real_inv_pos Z_full
                                                                                      uab_Z_full_pos))
                                                          (uab_full_pos_cert prefix w)))))
               (real_eq_refl _)
               (uab_minus_split (real_log (q w) (Hq w Hk))
                  (real_log (real_mult (real_temp_factor w)
                                       (real_inv_pos (uab_temp_sum prefix)
                                                     (uab_temp_sum_pos prefix)))
                            (uab_minp_pos_cert prefix w))
                  (real_log (real_mult (real_temp_factor w)
                                       (real_inv_pos Z_full uab_Z_full_pos))
                            (uab_full_pos_cert prefix w)))).
    + apply (real_distrib (q w)
                  (real_plus (real_log (q w) (Hq w Hk))
                             (real_opp (real_log (real_mult (real_temp_factor w)
                                                             (real_inv_pos (uab_temp_sum prefix)
                                                                           (uab_temp_sum_pos prefix)))
                                                 (uab_minp_pos_cert prefix w))))
                  (real_plus (real_log (real_mult (real_temp_factor w)
                                                  (real_inv_pos (uab_temp_sum prefix)
                                                                (uab_temp_sum_pos prefix)))
                                               (uab_minp_pos_cert prefix w))
                             (real_opp (real_log (real_mult (real_temp_factor w)
                                                             (real_inv_pos Z_full uab_Z_full_pos))
                                                  (uab_full_pos_cert prefix w))))).
  - apply (real_eq_sym _ _ (real_plus_zero real_zero)).
Qed.

(* 和级分解（尾项未求值形态）：Σ q‖full == Σ q‖minp + Σ tail *)
Lemma uab_kl_sum_split : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_eq (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab)
          (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                     (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _
           (real_list_sum Token
              (fun w : Token => real_plus (uab_kl_q_minp prefix q Hq_pos w)
                                          (uab_kl_tail prefix q Hq_pos w)) vocab) _).
  - apply (real_list_sum_ext Token (uab_kl_q_full prefix q Hq_pos)
              (fun w : Token => real_plus (uab_kl_q_minp prefix q Hq_pos w)
                                          (uab_kl_tail prefix q Hq_pos w)) vocab).
    exact (uab_kl_pointwise_split prefix q Hq_pos).
  - apply (real_list_sum_add Token (uab_kl_q_minp prefix q Hq_pos)
              (uab_kl_tail prefix q Hq_pos) vocab).
Qed.

(* 尾项求值：Σ q·(log minp − log full) == −log Z_aud（root kl_tail_eval 骨架） *)
Lemma uab_kl_tail_eval : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_eq (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)
          (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  assert (Hpt : forall w : Token,
             real_eq (uab_kl_tail prefix q Hq_pos w)
                     (real_mult (real_opp (real_log (Z_aud prefix)
                                                     (uab_Z_aud_pos_cert prefix))) (q w))).
  { intro w. unfold uab_kl_tail.
    destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    - apply (real_eq_trans _
                (real_mult (q w)
                   (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))) _).
      + apply (RealSetoid.real_eq_mult_compat (q w)
                   (real_plus (real_log (real_mult (real_temp_factor w)
                                                   (real_inv_pos (uab_temp_sum prefix)
                                                                 (uab_temp_sum_pos prefix)))
                                        (uab_minp_pos_cert prefix w))
                              (real_opp (real_log (real_mult (real_temp_factor w)
                                                              (real_inv_pos Z_full
                                                                             uab_Z_full_pos))
                                                   (uab_full_pos_cert prefix w))))
                   (q w)
                   (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                   (real_eq_refl _)
                   (uab_log_minp_minus_full prefix w)).
      + apply real_mult_comm.
    - pose proof (Hq_fail w Hd) as Hq0.
      apply (real_eq_trans real_zero
                (real_mult (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           real_zero)
                (real_mult (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           (q w))
                (real_eq_sym _ _
                   (real_mult_zero
                      (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))))
                (RealSetoid.real_eq_mult_compat
                   (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                   real_zero
                   (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                   (q w) (real_eq_refl _) (real_eq_sym (q w) real_zero Hq0))). }
  apply (real_eq_trans _
           (real_list_sum Token
              (fun w : Token =>
                 real_mult (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           (q w)) vocab) _).
  - apply (real_list_sum_ext Token (uab_kl_tail prefix q Hq_pos)
              (fun w : Token =>
                 real_mult (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           (q w)) vocab Hpt).
  - apply (real_eq_trans _
              (real_mult (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                         (real_list_sum Token q vocab)) _).
    + apply (real_list_sum_linear Token
                (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))) q vocab).
    + apply (real_eq_trans _
                (real_mult (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                           real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                  (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
                  (real_list_sum Token q vocab)
                  (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))) real_one
                  (real_eq_refl _) Hq_norm).
      * apply real_mult_one.
Qed.

(* 件 2 主恒等式（尾项已求值——任务书陈述形态） *)
Theorem real_kl_sum_split_list : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero),
  real_eq (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab)
          (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                     (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _
           (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                      (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)) _).
  - exact (uab_kl_sum_split prefix q Hq_norm Hq_pos Hq_fail).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _
             (real_eq_refl _) (uab_kl_tail_eval prefix q Hq_norm Hq_pos Hq_fail)).
Qed.

(* ============================================================ *)
(* 件 3（精确代价）：KL_list(minp ‖ full) == −log Z_aud           *)
(*   即截断代价 = 通过集质量亏损的对数（kept'==Z_aud，参照完整核） *)
(* ============================================================ *)

(* KL(dist‖dist) == 0（自 KL 归零） *)
Lemma uab_kl_self_zero : forall prefix : list Token,
  real_eq (real_list_sum Token
             (uab_kl_q_minp prefix (uab_minp_kernel prefix) (uab_minp_keep_pos prefix)) vocab)
          real_zero.
Proof.
  intro prefix.
  apply (real_eq_trans _ (real_list_sum Token (fun _ : Token => real_zero) vocab) _).
  - apply (real_list_sum_ext Token
              (uab_kl_q_minp prefix (uab_minp_kernel prefix) (uab_minp_keep_pos prefix))
              (fun _ : Token => real_zero) vocab).
    intro w. unfold uab_kl_q_minp.
    (* 全部展开暴露 match，再统一 case 分析（避免 delta 隐藏的 o 阻断抽象） *)
    unfold uab_minp_kernel, real_minp_markov_kernel, uab_minp_keep_pos.
    destruct (real_minp_keep_dec prefix w) as [Hk | Hd].
    + apply (real_eq_trans _
                  (real_mult (real_mult (real_temp_factor w)
                                        (real_inv_pos (uab_temp_sum prefix)
                                                      (uab_temp_sum_pos prefix)))
                             real_zero) _).
      * apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
                  (real_plus_opp (real_log (real_mult (real_temp_factor w)
                                                      (real_inv_pos (uab_temp_sum prefix)
                                                                    (uab_temp_sum_pos prefix)))
                                           (uab_minp_pos_cert prefix w)))).
      * apply real_mult_zero.
    + apply real_eq_refl.
  - apply uab_list_sum_zero.
Qed.

Theorem real_minp_kl_cost : forall prefix : list Token,
  real_eq (real_list_sum Token
             (uab_kl_q_full prefix (uab_minp_kernel prefix) (uab_minp_keep_pos prefix)) vocab)
          (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix))).
Proof.
  intro prefix.
  pose proof (uab_kl_sum_split prefix (uab_minp_kernel prefix)
                (real_minp_markov_kernel_normalized Token vocab real_temp_factor
                   real_minp_keep real_minp_keep_dec uab_temp_sum_pos prefix)
                (uab_minp_keep_pos prefix) (uab_minp_fail_zero prefix)) as Hsplit.
  pose proof (uab_kl_tail_eval prefix (uab_minp_kernel prefix)
                (real_minp_markov_kernel_normalized Token vocab real_temp_factor
                   real_minp_keep real_minp_keep_dec uab_temp_sum_pos prefix)
                (uab_minp_keep_pos prefix) (uab_minp_fail_zero prefix)) as Htail.
  pose proof (uab_kl_self_zero prefix) as Hself.
  apply (real_eq_trans _
           (real_plus (real_list_sum Token
                         (uab_kl_q_minp prefix (uab_minp_kernel prefix)
                                       (uab_minp_keep_pos prefix)) vocab)
                      (real_list_sum Token
                         (uab_kl_tail prefix (uab_minp_kernel prefix)
                                       (uab_minp_keep_pos prefix)) vocab)) _).
  - exact Hsplit.
  - apply (real_eq_trans _
              (real_plus (real_list_sum Token
                            (uab_kl_q_minp prefix (uab_minp_kernel prefix)
                                          (uab_minp_keep_pos prefix)) vocab)
                         (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))) _).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) Htail).
    + apply (real_eq_trans _
                (real_plus real_zero
                           (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))) _).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ Hself (real_eq_refl _)).
      * apply uab_plus_zero_l.
Qed.

(* ============================================================ *)
(* 件 4（eps 最优性）：KL_list(q ‖ minp) ≤ KL_list(q ‖ full) + eps *)
(*   由件 2 分解 + 尾项 = −log Z_aud ≥ 0（件 5）+ eps 余量；        *)
(*   方向纪律：仅截断侧度量，不主张 KL(full‖minp)。               *)
(* ============================================================ *)

Lemma uab_le_plus_nonneg_r : forall a c : Real,
  real_le real_zero c -> real_le a (real_plus a c).
Proof.
  intros a c H0c.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a c)
           (real_eq_sym (real_plus a real_zero) a (real_plus_zero a))).
  apply (real_le_plus_compat a a real_zero c (real_le_refl a) H0c).
Qed.

Theorem real_minp_projection_eps : forall (prefix : list Token) (q : Token -> Real)
  (Hq_norm : real_eq (real_list_sum Token q vocab) real_one)
  (Hq_pos : forall w : Token, real_minp_keep prefix w -> real_lt real_zero (q w))
  (Hq_fail : forall w : Token, Not (real_minp_keep prefix w) -> real_eq (q w) real_zero)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
          (real_plus (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab) eps).
Proof.
  intros prefix q Hq_norm Hq_pos Hq_fail eps Heps.
  pose proof (uab_kl_sum_split prefix q Hq_norm Hq_pos Hq_fail) as Hsplit.
  pose proof (uab_kl_tail_eval prefix q Hq_norm Hq_pos Hq_fail) as Htail.
  pose proof (real_opp_log_Z_aud_nonneg prefix) as Hnonneg.
  assert (HT : real_le real_zero
                 (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)).
  { apply (RealSetoid.real_le_id_r real_zero
             (real_opp (real_log (Z_aud prefix) (uab_Z_aud_pos_cert prefix)))
             (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)
             (real_eq_sym _ _ Htail) Hnonneg). }
  assert (HT2 : real_le real_zero
                  (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab) eps)).
  { apply (real_le_plus_compat real_zero
             (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab)
             real_zero eps HT
             (RealSetoid.real_lt_le_iff_req real_zero eps (inl Heps))). }
  assert (H1 : real_le (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                       (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                                  (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos)
                                                              vocab)
                                             eps))).
  { apply uab_le_plus_nonneg_r. exact HT2. }
  assert (H2 : real_eq (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                                  (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos)
                                                              vocab)
                                             eps))
                       (real_plus (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab)
                                  eps)).
  { apply (real_eq_trans _
              (real_plus (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                                    (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab))
                         eps) _).
    - apply (real_plus_assoc (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab) eps).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _
                (real_eq_sym _ _ Hsplit) (real_eq_refl eps)). }
  apply (RealSetoid.real_le_id_r
           (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
           (real_plus (real_list_sum Token (uab_kl_q_minp prefix q Hq_pos) vocab)
                      (real_plus (real_list_sum Token (uab_kl_tail prefix q Hq_pos) vocab) eps))
           (real_plus (real_list_sum Token (uab_kl_q_full prefix q Hq_pos) vocab) eps)
           H2 H1).
Qed.

End UpAuditBridge.
End AuditBridge.

(* ---------- UpPredRelax ---------- *)
From Stdlib Require Import Arith.
(* ============================================================ *)
(* UpPredRelax.v —— B8 升级：预测区弛豫单调（假设→定性推论最小件） *)
(* 日期：2026-09-07。源：热点扫描 B8（分析-219平凡定理热点扫描）    *)
(* 件 4 heat_relaxation_decreasing（预测 1 热弛豫单调衰减）        *)
(* 件 5a fluctuation_scale_decreasing（预测 4，镜像 L1671 模板）   *)
(* 件 5b landauer_bound_pos（预测 3，三正相乘）                    *)
(* 件 5c disturbance_hierarchical_transitive / chain（预测 6）     *)
(* 件 5d total_loss_multi_epoch_decreasing（预测 7，多 epoch 链）   *)
(* 诚实边界（在册边界 #3）：预测区 1–7 无具体动力学/能量定义可消费  *)
(*   （equilibrium_dist、prediction_landauer 等均无构造性定义），   *)
(*   完全定理化不可行；本文件为"假设→定性推论"最小件，全部额外      *)
(*   前提（正性/单调/log 正性）显式声明为 Section Variable，零隐藏。 *)
(*   预测 5（cross_domain_scaling，sigT 前提）无定量杠杆，不做。    *)
(* 纪律：纯构造性 / Set 层 / 零 Axiom / 零 Admitted / 零经典。      *)
(* ============================================================ *)


(* ============================================================ *)
(* 件 4：预测 1 热弛豫的单调衰减                                  *)
(*   前提：heat_relaxation_exponential（根内 Prediction1 同批）+   *)
(*   γ ≥ 0、T₀ ≥ 0、of_nat 单调（显式新增，见诚实边界）。          *)
(* ============================================================ *)
Section PredRelaxHeat.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.

Variable temperature_difference : nat -> R.
Variable gamma : R.
Variable of_nat : nat -> R.
Variable temperature_difference0 : R.

Variable gamma_nonneg : le zero gamma.
Variable temperature_difference0_nonneg : le zero temperature_difference0.
Variable of_nat_mono : forall t : nat, le (of_nat t) (of_nat (Nat.succ t)).

Variable heat_relaxation_exponential :
  forall t : nat,
    Id (temperature_difference t)
       (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0).

(* 弛豫单调衰减：T(S t) ≤ T(t)
   （γ·of_nat 单调 ⟹ exp_neg 反序单调 ⟹ 乘 T₀ ≥ 0 保序）。 *)
Theorem heat_relaxation_decreasing : forall t : nat,
  le (temperature_difference (Nat.succ t)) (temperature_difference t).
Proof.
  intro t.
  assert (Hg : le (mult gamma (of_nat t)) (mult gamma (of_nat (Nat.succ t)))).
  { (* 接口 le_mult_compat_weak 为右乘形态：经 mult_comm 双端换形 *)
    apply (le_id_l (mult gamma (of_nat t)) (mult (of_nat t) gamma)
                   (mult gamma (of_nat (Nat.succ t)))).
    - apply (mult_comm gamma (of_nat t)).
    - apply (le_id_r (mult (of_nat t) gamma) (mult (of_nat (Nat.succ t)) gamma)
                     (mult gamma (of_nat (Nat.succ t)))).
      + apply (mult_comm (of_nat (Nat.succ t)) gamma).
      + apply (le_mult_compat_weak (of_nat t) (of_nat (Nat.succ t)) gamma).
        * exact gamma_nonneg.
        * exact (of_nat_mono t). }
  assert (He : le (exp_neg (mult gamma (of_nat (Nat.succ t))))
                  (exp_neg (mult gamma (of_nat t))))
    by exact (exp_neg_le_decr _ _ Hg).
  assert (Hm : le (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                  (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0))
    by exact (le_mult_compat_weak _ _ temperature_difference0
              temperature_difference0_nonneg He).
  apply (le_id_l (temperature_difference (Nat.succ t))
                 (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                 (temperature_difference t)).
  - exact (heat_relaxation_exponential (Nat.succ t)).
  - apply (le_id_r (mult (exp_neg (mult gamma (of_nat (Nat.succ t)))) temperature_difference0)
                   (mult (exp_neg (mult gamma (of_nat t))) temperature_difference0)
                   (temperature_difference t)).
    + exact (id_sym (heat_relaxation_exponential t)).
    + exact Hm.
Qed.

End PredRelaxHeat.

(* ============================================================ *)
(* 件 5a：预测 4 涨落标度的单调衰减（镜像根内 L1671               *)
(*   prediction_fluctuation_scale 的已验收升级模板）。             *)
(* ============================================================ *)
Section PredRelaxFluct.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let exp_neg := @exp_neg RI.
Let le := @le RI.

Variable prob_negative_entropy : R -> R.
Variable k_B : R.
Variable k_B_pos : lt zero k_B.

Variable fluctuation_scale :
  forall N : R,
    Id (prob_negative_entropy N)
       (exp_neg (mult N (inv_pos k_B k_B_pos))).

(* 涨落概率随 N 单调衰减：P(N+1) ≤ P(N)。
   核：N ≤ N+1 乘 1/k_B ≥ 0（L1671 同链），exp_neg 反序。 *)
Theorem fluctuation_scale_decreasing : forall N : R,
  le (prob_negative_entropy (plus N one)) (prob_negative_entropy N).
Proof.
  intro N.
  assert (Hcore : le (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                     (exp_neg (mult N (inv_pos k_B k_B_pos)))).
  { apply exp_neg_le_decr.
    apply (le_mult_compat_weak N (plus N one) (inv_pos k_B k_B_pos)).
    - apply (lt_le_iff _ _). left. apply inv_pos_pos.
    - apply le_plus_nonneg_r. exact (lt_le_iff _ _ (inl one_pos)). }
  apply (le_id_l (prob_negative_entropy (plus N one))
                 (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                 (prob_negative_entropy N)).
  - exact (fluctuation_scale (plus N one)).
  - apply (le_id_r (exp_neg (mult (plus N one) (inv_pos k_B k_B_pos)))
                   (exp_neg (mult N (inv_pos k_B k_B_pos)))
                   (prob_negative_entropy N)).
    + exact (id_sym (fluctuation_scale N)).
    + exact Hcore.
Qed.

End PredRelaxFluct.

(* ============================================================ *)
(* 件 5b：预测 3 Landauer 界的正性（假设→定性推论最小件）。        *)
(*   前提：prediction_landauer（根内 Prediction3 同批）+ k_B>0、   *)
(*   T>0、log 2>0（显式新增；接口 log 无序字段，见诚实边界）。     *)
(* ============================================================ *)
Section PredRelaxLandauer.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let mult := @mult RI.
Let log := @log RI.
Let le := @le RI.
Let lt := @lt RI.

Variable E_min : R.
Variable k_B : R.
Variable T_landauer : R.

Variable k_B_pos : lt zero k_B.
Variable T_pos : lt zero T_landauer.
Variable log_two_pos : lt zero (log (plus one one)).

Variable prediction_landauer :
  Id E_min (mult k_B (mult T_landauer (log (plus one one)))).

(* Landauer 界为正：E_min = k_B·T·log 2 > 0（三正相乘 + 恒等换形）。 *)
Theorem landauer_bound_pos : lt zero E_min.
Proof.
  assert (Hinner : lt zero (mult T_landauer (log (plus one one))))
    by exact (mult_positive T_landauer (log (plus one one)) T_pos log_two_pos).
  assert (Houter : lt zero (mult k_B (mult T_landauer (log (plus one one)))))
    by exact (mult_positive k_B (mult T_landauer (log (plus one one)))
                              k_B_pos Hinner).
  apply (lt_id_r zero _ E_min (id_sym prediction_landauer) Houter).
Qed.

End PredRelaxLandauer.

(* ============================================================ *)
(* 件 5c：预测 6 层级稳定性的扰动传递（假设→定性推论最小件）。     *)
(* ============================================================ *)
Local Open Scope nat_scope.

Section PredRelaxHier.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.

Let R := @R RI.
Let le := @le RI.
Let PropType := @PropositionConvergenceCore.Proposition RI SS.

Variable disturbance : PropType -> R.
Variable hierarchical_relation : PropType -> PropType -> Set.

Variable hierarchical_stability_prediction :
  forall (upper lower : PropType),
    hierarchical_relation upper lower ->
    le (disturbance upper) (disturbance lower).

(* 两步传递：上层扰动 ≤ 中层扰动 ≤ 下层扰动 ⟹ 上 ≤ 下。 *)
Theorem disturbance_hierarchical_transitive : forall (u m l : PropType),
  hierarchical_relation u m -> hierarchical_relation m l ->
  le (disturbance u) (disturbance l).
Proof.
  intros u m l Hum Hml.
  apply (le_trans (disturbance u) (disturbance m) (disturbance l)).
  - exact (hierarchical_stability_prediction u m Hum).
  - exact (hierarchical_stability_prediction m l Hml).
Qed.

(* 有限链版本：沿层级链 n 步，扰动单调不增
   （le_refl + le_trans 的 nat 归纳；链前提逐点显式）。 *)
Theorem disturbance_chain_decreasing : forall (chain : nat -> PropType),
  (forall k : nat, hierarchical_relation (chain k) (chain (Nat.succ k))) ->
  forall (k n : nat), le (disturbance (chain k)) (disturbance (chain (k + n))).
Proof.
  intros chain Hrel k n.
  induction n as [| n IH].
  - rewrite Nat.add_0_r. apply le_refl.
  - replace (k + Datatypes.S n) with (Nat.succ (k + n))
      by apply (eq_sym (Nat.add_succ_r k n)).
    apply (le_trans (disturbance (chain k)) (disturbance (chain (k + n)))
                    (disturbance (chain (Nat.succ (k + n))))).
    + exact IH.
    + exact (hierarchical_stability_prediction (chain (k + n))
                                               (chain (Nat.succ (k + n)))
                                               (Hrel (k + n))).
Qed.

End PredRelaxHier.

(* ============================================================ *)
(* 件 5d：预测 7 语言模型结构相关的多 epoch 损失下降链             *)
(*   （假设→定性推论最小件；单步相关性前提逐点显式）。             *)
(* ============================================================ *)
Section PredRelaxLM.

Context {RI : RealInterfaceEnhanced}.

Let R := @R RI.
Let le := @le RI.

Variable Token : Set.
Variable model : nat -> list Token.
Variable grammar_error : list Token -> R.
Variable total_loss : list Token -> R.

Variable loss_structure_correlation :
  forall epoch : nat,
    le (grammar_error (model epoch)) (grammar_error (model (Nat.succ epoch))) ->
    le (total_loss (model epoch)) (total_loss (model (Nat.succ epoch))).

(* 多 epoch 损失下降链：grammar_error 逐 epoch 单调
   ⟹ total_loss 沿任意 n 步单调不增。 *)
Theorem total_loss_multi_epoch_decreasing : forall (start n : nat),
  (forall k : nat, le (grammar_error (model k)) (grammar_error (model (Nat.succ k)))) ->
  le (total_loss (model start)) (total_loss (model (start + n))).
Proof.
  intros start n Hg.
  induction n as [| n IH].
  - rewrite Nat.add_0_r. apply le_refl.
  - replace (start + Datatypes.S n) with (Nat.succ (start + n))
      by apply (eq_sym (Nat.add_succ_r start n)).
    apply (le_trans (total_loss (model start)) (total_loss (model (start + n)))
                    (total_loss (model (Nat.succ (start + n))))).
    + exact IH.
    + exact (loss_structure_correlation (start + n) (Hg (start + n))).
Qed.

End PredRelaxLM.

Local Close Scope nat_scope.

(* ---------- UpPLA ---------- *)
From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Section UpPLAScopeGuard.

Local Notation S := Datatypes.S (only parsing).
Local Notation O := Datatypes.O (only parsing).

(* ===================================================================== *)
(* UpPLA.v — PLA v2 Coq 落地：p-adic 分层商 + 残基契约 + VCA 估值账户机      *)
(*                                                                       *)
(* 二轮圆桌头部候选（3 票）正式立项。理论来源：                              *)
(*   ROUNDTABLE2.md 席 6 段落末尾【PLA v2 终稿】四击正面收口 + VCA 杂交；      *)
(*   排队席位方案-二轮成果Coq化-20260907.md Q1 条目。                        *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；零 eps、零序比较、零见证借贷。                 *)
(* 纪律：纯构造性（无 Axiom/Admitted/Parameter/Abort）；语句零 Prop           *)
(* （Set 层 tid 恒等型 + nle 序型 + sumbool 判定分支）；stdlib only。         *)
(*                                                                       *)
(* 四件：                                                                 *)
(*   件 1  p-adic 估值机器 vp（乘法可加 + 整除表征）                          *)
(*   件 2  分层商主件（layer_closed / layer_decide / pla_stratified_quotient  *)
(*         + 席 5 分岔反例收编对照定理）                                     *)
(*   件 3  残基契约显式化（contract 双档，调度器输入参数非隐藏前提）            *)
(*   件 4  VCA 估值账户机（入场费可判定 / 耗散单调 / 进位清偿调度）             *)
(* ===================================================================== *)


Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建：tid 恒等型 / nle 序型 / 判定存活工具                        *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive cwe_tid (A : Type) : A -> A -> Type := cwe_tid_refl : forall x : A, cwe_tid A x x.

Definition cwe_tid_sym (A : Type) (x y : A) (H : cwe_tid A x y) : cwe_tid A y x :=
  match H in cwe_tid _ a b return cwe_tid _ b a with
  | cwe_tid_refl _ a0 => @cwe_tid_refl _ a0
  end.

Definition cwe_tid_trans (A : Type) (x y z : A) (H1 : cwe_tid A x y) (H2 : cwe_tid A y z) :
  cwe_tid A x z :=
  match H1 in cwe_tid _ a b return cwe_tid _ b z -> cwe_tid _ a z with
  | cwe_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition cwe_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : cwe_tid A x y) :
  cwe_tid B (f x) (f y) :=
  match H in cwe_tid _ a b return cwe_tid B (f a) (f b) with
  | cwe_tid_refl _ a0 => @cwe_tid_refl _ (f a0)
  end.

(* Set 层自然数序型（k < m 编码为 nle (S k) m） *)
Inductive cwe_nle (n : nat) : nat -> Set :=
| cwe_nle_n : cwe_nle n n
| cwe_nle_S : forall m : nat, cwe_nle n m -> cwe_nle n (S m).

Ltac tidE H :=
  pose proof (match H in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as HE.

(* bool 恒等矛盾关闭器：H1 : cwe_tid bool X true、H2 : cwe_tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* Set 层 cwe_nle 基本件 *)
Lemma cwe_leb_refl_tid : forall a : nat, cwe_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply cwe_tid_refl.
Qed.

Lemma cwe_leb_S : forall a m : nat,
  cwe_tid bool (Nat.leb a m) true -> cwe_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply cwe_tid_refl.
    + change (cwe_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply cwe_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint cwe_nle_lebF (a b : nat) (H : cwe_nle a b) {struct H} :
  cwe_tid bool (Nat.leb a b) true :=
  match H as H0 in cwe_nle _ bb
  return cwe_tid bool (Nat.leb a bb) true with
  | cwe_nle_n _ => cwe_leb_refl_tid a
  | cwe_nle_S _ m H1 => cwe_leb_S a m (cwe_nle_lebF a m H1)
  end.

Definition cwe_nle_leb (b a : nat) (H : cwe_nle a b) : cwe_tid bool (Nat.leb a b) true :=
  cwe_nle_lebF a b H.

(* cwe_nle -> nat ≤ 提取（仅证明内部推理用；可重复调用，自动起新名） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (cwe_nle_leb _ _ H) in cwe_tid _ x y return x = y with
        | cwe_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma cwe_nle_SS : forall a b : nat, cwe_nle a b -> cwe_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply cwe_nle_n.
  - apply cwe_nle_S. exact IH.
Qed.

Lemma cwe_nle_0 : forall m : nat, cwe_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply cwe_nle_n.
  - apply cwe_nle_S. exact IH.
Qed.

Lemma cwe_nle_of_leb : forall b a : nat,
  cwe_tid bool (Nat.leb a b) true -> cwe_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply cwe_nle_n.
    + change (cwe_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply cwe_nle_0.
    + exact (cwe_nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ → cwe_tid bool (leb) true 桥（leb_le 的 bool 封装） *)
Lemma cwe_lebT : forall a b : nat, (a <= b)%nat -> cwe_tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply cwe_tid_refl.
Qed.


Lemma cwe_nle_trans : forall a b c : nat, cwe_nle a b -> cwe_nle b c -> cwe_nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply cwe_nle_S. exact IH.
Qed.

(* cwe_nle 前驱消解：cwe_nle (S a) (S b) -> cwe_nle a b *)
Lemma cwe_nle_pred : forall a b : nat, cwe_nle (S a) (S b) -> cwe_nle a b.
Proof.
  intros a b H. apply cwe_nle_of_leb.
  exact (cwe_nle_leb (S b) (S a) H).
Qed.

Lemma cwe_nle_add_r : forall a b : nat, cwe_nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply cwe_nle_0.
  - exact (cwe_nle_SS a1 (a1 + b) (IH b)).
Qed.


(* cwe_nle (S O) O 荒谬件（索引不交配的空消去，合法关闭任意 Set 目标） *)
Lemma cwe_nle_10_absurd : forall P : Type, cwe_nle (S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

(* Z 层严格序 → cwe_nle 编码桥：0 ≤ a < b ⟹ cwe_nle (S (to_nat a)) (to_nat b) *)
Lemma cwe_zle_to_nle_S : forall a b : Z, (0 <= a)%Z -> (a < b)%Z ->
  cwe_nle (S (Z.to_nat a)) (Z.to_nat b).
Proof.
  intros a b Ha Hlt.
  assert (Hb : (0 <= b)%Z) by lia.
  apply cwe_nle_of_leb.
  assert (Hleb : (Nat.leb (S (Z.to_nat a)) (Z.to_nat b)) = true).
  { apply Nat.leb_le.
    exact (proj1 (Z2Nat.inj_lt a b Ha Hb) Hlt). }
  rewrite Hleb. apply cwe_tid_refl.
Qed.

(* n≠0 ⟹ |n| 的 nat 编码 ≥ (S O) *)
Lemma cwe_to_nat_abs_pos : forall n : Z,
  cwe_tid bool (Z.eqb n 0) false -> cwe_nle (S O) (Z.to_nat (Z.abs n)).
Proof.
  intros n H. tidE H.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  apply (cwe_zle_to_nle_S 0 (Z.abs n)).
  - lia.
  - pose proof (proj2 (Z.abs_pos n) Hne). lia.
Qed.

(* |x| ≥ (S O) ⟹ x ≠ 0 的 bool 形 *)
Lemma eqb0_false_of_pos : forall x : Z,
  cwe_nle (S O) (Z.to_nat (Z.abs x)) -> cwe_tid bool (Z.eqb x 0) false.
Proof.
  intros x H. destruct (Z.eqb x 0) eqn:HEq.
  - apply (proj1 (Z.eqb_eq _ _)) in HEq. rewrite HEq in H.
    exact (cwe_nle_10_absurd _ H).
  - apply cwe_tid_refl.
Qed.

(* ===================================================================== *)
(* 件 1. p-adic 估值机器                                                  *)
(* ===================================================================== *)

(* p 的 Z 形 / 整除测试 / p^k / p^k 整除测试 *)
Definition pZ (p : nat) : Z := Z.of_nat p.
Definition dvdtest (p : nat) (x : Z) : bool := Z.eqb (Z.modulo x (pZ p)) 0.
Definition powZN (p k : nat) : Z := Z.pow (pZ p) (Z.of_nat k).
Definition dwtest (p k : nat) (x : Z) : bool := Z.eqb (Z.modulo x (powZN p k)) 0.

(* 燃料式估值计数。vp p 0 := 0 专用编码（零态由 Z.eqb 守卫直派 0，避免
   nat 编码无穷；消耗方以 Z.eqb n 0 守卫非零——报告注 1）。 *)
Fixpoint vpF (p : nat) (f : nat) (n : Z) {struct f} : nat :=
  match f with
  | O => O
  | S g =>
      if Z.eqb n 0 then O
      else if dvdtest p n then S (vpF p g (Z.div n (pZ p)))
      else O
  end.

(* 公开估值：燃料取 |n|+1（n≠0 且 p≥2 时每步 |n| 至少折半，燃料充分） *)
Definition vp (p : nat) (n : Z) : nat := vpF p (S (Z.to_nat (Z.abs n))) n.

(* 关键递减：p≥2、n≠0、p∣n ⟹ |n/p| < |n|（cwe_nle (S k) m 编码 k<m） *)
Lemma zdiv_abs_decr : forall (p : nat) (n : Z), (2 <= p)%nat ->
  cwe_tid bool (Z.eqb n 0) false -> cwe_tid bool (dvdtest p n) true ->
  cwe_nle (S (Z.to_nat (Z.abs (Z.div n (pZ p))))) (Z.to_nat (Z.abs n)).
Proof.
  intros p n Hp Hnz Hd.
  tidE Hnz.
  pose proof (match Hd in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hp. }
  assert (Hpp : (0 <= pZ p)%Z) by lia.
  assert (Hpz0 : pZ p <> 0) by lia.
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hex : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hdm. rewrite Hmod in Hdm. lia. }
  assert (Hq0 : Z.div n (pZ p) <> 0).
  { intro Hc. rewrite Hc in Hex. lia. }
  assert (Hqa : (0 < Z.abs (Z.div n (pZ p)))%Z).
  { apply (proj2 (Z.abs_pos (Z.div n (pZ p)))). exact Hq0. }
  assert (Habsm : Z.abs n = pZ p * Z.abs (Z.div n (pZ p))).
  { rewrite Hex at 1. rewrite Z.abs_mul. rewrite (Z.abs_eq (pZ p) Hpp).
    reflexivity. }
  assert (Hm2 : (2 * Z.abs (Z.div n (pZ p)) <= Z.abs n)%Z).
  { rewrite Habsm. apply Z.mul_le_mono_nonneg_r.
    - apply Z.abs_nonneg.
    - exact Hpz. }
  assert (Hlt : (Z.abs (Z.div n (pZ p)) < Z.abs n)%Z) by lia.
  apply cwe_zle_to_nle_S.
  - apply Z.abs_nonneg.
  - exact Hlt.
Qed.

(* 除法保持非零：p≥2、n≠0、p∣n ⟹ n/p ≠ 0（bool 形） *)
Lemma zdiv_nz : forall (p : nat) (n : Z), (2 <= p)%nat ->
  cwe_tid bool (Z.eqb n 0) false -> cwe_tid bool (dvdtest p n) true ->
  cwe_tid bool (Z.eqb (Z.div n (pZ p)) 0) false.
Proof.
  intros p n Hp Hnz Hd.
  assert (Hpz : (2 <= pZ p)%Z).
  { unfold pZ. apply (proj1 (Nat2Z.inj_le 2 p)). exact Hp. }
  assert (Hpz0 : pZ p <> 0) by lia.
  tidE Hnz.
  pose proof (match Hd in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as HE2.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  assert (Hmod : Z.modulo n (pZ p) = 0) by (apply (proj1 (Z.eqb_eq _ _)); exact HE2).
  assert (Hdm : n = pZ p * (Z.div n (pZ p))).
  { pose proof (Z.div_mod n (pZ p) Hpz0) as Hd0. rewrite Hmod in Hd0. lia. }
  apply eqb0_false_of_pos.
  apply (cwe_zle_to_nle_S 0 (Z.abs (Z.div n (pZ p)))).
  - lia.
  - apply (proj2 (Z.abs_pos (Z.div n (pZ p)))).
    intro Hc. rewrite Hc in Hdm. lia.
Qed.

(* 燃料无关性：燃料均盖住 |n| 时计数唯一 *)
Lemma vpF_indep : forall (p B : nat), (2 <= p)%nat ->
  forall (f1 f2 : nat) (n : Z),
    cwe_nle (Z.to_nat (Z.abs n)) B ->
    cwe_tid bool (Z.eqb n 0) false ->
    cwe_nle (Z.to_nat (Z.abs n)) f1 ->
    cwe_nle (Z.to_nat (Z.abs n)) f2 ->
    cwe_tid nat (vpF p f1 n) (vpF p f2 n).
Proof.
  intros p B Hp. induction B as [| B1 IB]; intros f1 f2 n HnB Hnz Hf1 Hf2.
  - assert (H1 := cwe_to_nat_abs_pos n Hnz).
    pose proof (cwe_nle_trans _ _ _ H1 HnB) as HC. inversion HC.
  - destruct f1 as [| g1].
    + assert (H1 := cwe_to_nat_abs_pos n Hnz).
      pose proof (cwe_nle_trans _ _ _ H1 Hf1) as HC. inversion HC.
    + destruct f2 as [| g2].
      * assert (H1 := cwe_to_nat_abs_pos n Hnz).
        pose proof (cwe_nle_trans _ _ _ H1 Hf2) as HC. inversion HC.
      * cbn [vpF]. tidE Hnz. rewrite HE.
        destruct (dvdtest p n) eqn:Hd.
        -- (* p ∣ n：两边同进入位支，递归比较 n/p 的计数 *)
           assert (Hdt : cwe_tid bool (dvdtest p n) true)
             by (rewrite Hd; apply cwe_tid_refl).
           apply (cwe_tid_cong S).
           apply IB with (n := Z.div n (pZ p)).
           ++ exact (cwe_nle_pred _ _
                 (cwe_nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) HnB)).
           ++ exact (zdiv_nz p n Hp Hnz Hdt).
           ++ exact (cwe_nle_pred _ _
                 (cwe_nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf1)).
           ++ exact (cwe_nle_pred _ _
                 (cwe_nle_trans _ _ _ (zdiv_abs_decr p n Hp Hnz Hdt) Hf2)).
        -- (* p ∤ n：else 支直派 O（destruct 已代入，iota 归约即闭） *)
           apply cwe_tid_refl.
Qed.

End UpPLAScopeGuard.

(* ---------- UpStepKLM3 ---------- *)
From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
(* ============================================================ *)
(* UpStepKLM3.v —— step_kl 放电的 M3 迭代版 Real 层镜像            *)
(* 论文 1 定理 4.5/4.8（策略迭代向后 KL 递推 + 真几何率收缩）的      *)
(* Real 层 list 离散状态世界对应物。                               *)
(*   M3.0 基础定义：离散状态表 m3_states、list 版 KL（m3_kl_list，   *)
(*         逐项 real_kl_term 折叠）、几何插值策略迭代序列 m3_pi_seq   *)
(*         （π_{t+1}(i) := π*(i)^η·π_t(i)^{1−η}/Z，sigT 打包迭代：   *)
(*         策略 + 逐点正性 + 配分函数正性 + 归一化四件套同步携带）、  *)
(*         几何率底幂 m3_rpow (1−η)^t、误差 nat 累积 m3_nmul。       *)
(*   M3.1 单步向后 KL 递推 real_iter_kl_step：                      *)
(*         KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1}) + eps *)
(*         （根内 policy_iter_backward_kl_step_le 的 eps 化镜像：    *)
(*           M2 换向实例 + Gibbs 下界 + eps 对半吸收）。             *)
(*   M3.2 真几何率迭代 real_iter_kl_geom：                          *)
(*         KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps                 *)
(*         （根内 policy_iter_kl_geom_step / policy_iter_kl_geom_iter *)
(*           的 eps 化镜像：M2 单步 + nat 归纳）。                   *)
(* 全部 Real 层顶层名（real_kl_term/real_list_sum/real_step_next），  *)
(* Or 编码 le。                                                    *)
(* 红线：零 公理/搁置；Set 层语句；全 Qed；可提取。             *)
(* ============================================================ *)

Import ListNotations.
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== M3.0 基础定义 ========== *)

(* 离散状态表：n 个状态 [0;1;...;n-1]（list 离散状态世界） *)
Definition m3_states (n : nat) : list nat := seq 0 n.

(* KL 的 list 版：逐项 real_kl_term 折叠求和 *)
Definition m3_kl_list (n : nat) (f g : nat -> Real)
    (Hf : forall i : nat, real_lt real_zero (f i))
    (Hg : forall i : nat, real_lt real_zero (g i)) : Real :=
  real_list_sum nat
    (fun i : nat => real_kl_term (f i) (g i) (Hf i) (Hg i))
    (m3_states n).

(* 几何率底 κ := 1−η *)
Definition m3_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* κ 的 t 次幂（nat 重复乘）※ S 遮蔽 Datatypes.S，须限定名 *)
Fixpoint m3_rpow (a : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_one
  | Datatypes.S t' => real_mult a (m3_rpow a t')
  end.

(* t·x（nat 重复加；逐步误差 eps 的 t 步累积） *)
Fixpoint m3_nmul (k : nat) (x : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S k' => real_plus x (m3_nmul k' x)
  end.

(* 1+1 > 0（对半预算的分母） *)
Lemma m3_two_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one real_one)
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              kl_zero_plus_zero)
           (real_lt_plus_compat real_zero real_one real_zero real_one
              real_lt_zero_one real_lt_zero_one)).
Qed.

(* eps 对半：d := eps·inv(1+1)（M3.1 的双 eps 预算合一） *)
Definition m3_half (eps : Real) : Real :=
  real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos).

Lemma m3_half_pos : forall eps : Real,
  real_lt real_zero eps -> real_lt real_zero (m3_half eps).
Proof.
  intros eps Heps. unfold m3_half.
  exact (real_mult_positive eps
           (real_inv_pos (real_plus real_one real_one) m3_two_pos)
           Heps
           (real_inv_pos_pos (real_plus real_one real_one) m3_two_pos)).
Qed.

Lemma m3_half_double_eq : forall eps : Real,
  real_eq (real_plus (m3_half eps) (m3_half eps)) eps.
Proof.
  intros eps. unfold m3_half.
  set (dd := real_mult eps (real_inv_pos (real_plus real_one real_one) m3_two_pos)).
  set (two := real_plus real_one real_one).
  apply (real_eq_trans (real_plus dd dd) (real_mult two dd)).
  - exact (real_eq_trans (real_plus dd dd)
             (real_plus (real_mult real_one dd) (real_mult real_one dd))
             (real_mult two dd)
             (RealSetoid.real_eq_plus_compat dd dd
                (real_mult real_one dd) (real_mult real_one dd)
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd))
                (real_eq_sym (real_mult real_one dd) dd (kl_mult_one_l dd)))
             (kl_sum_prod_r real_one real_one dd)).
  - exact (real_eq_trans (real_mult two dd)
             (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
             eps
             (kl_swap3 two eps (real_inv_pos two m3_two_pos))
             (real_eq_trans
                (real_mult eps (real_mult two (real_inv_pos two m3_two_pos)))
                (real_mult eps real_one)
                eps
                (RealSetoid.real_eq_mult_compat eps
                   (real_mult two (real_inv_pos two m3_two_pos)) eps real_one
                   (real_eq_refl eps)
                   (real_inv_pos_correct two m3_two_pos))
                (real_mult_one eps))).
Qed.

(* ========== 环 / 序辅助 ========== *)

(* η + (1−η) == 1 *)
Lemma m3_ring_eta_kappa : forall eta : Real,
  real_eq (real_plus eta (m3_kappa eta)) real_one.
Proof.
  intros eta. destruct eta as [v Hv]. unfold m3_kappa.
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* η < 1 ⟹ 0 < 1−η *)
Lemma m3_kappa_pos : forall eta : Real,
  real_lt eta real_one -> real_lt real_zero (m3_kappa eta).
Proof.
  intros eta Hlt. unfold m3_kappa.
  exact (real_eq_lt_lt real_zero (real_plus eta (real_opp eta))
           (real_plus real_one (real_opp eta))
           (real_eq_sym (real_plus eta (real_opp eta)) real_zero
              (real_plus_opp eta))
           (real_lt_plus_compat_lt_le eta real_one (real_opp eta)
              (real_opp eta) Hlt (real_le_refl (real_opp eta)))).
Qed.

(* 0 < η ⟹ 1−η ≤ 1 *)
Lemma m3_kappa_le_one : forall eta : Real,
  real_lt real_zero eta -> real_le (m3_kappa eta) real_one.
Proof.
  intros eta Hpos. unfold m3_kappa. apply kl_lt_le_bridge.
  set (X := real_plus real_one (real_opp eta)).
  assert (Hstep1 : real_lt (real_plus real_zero X) (real_plus eta X))
    by exact (real_lt_plus_compat_lt_le real_zero eta X X Hpos (real_le_refl X)).
  assert (Hstep2 : real_lt (real_plus real_zero X) real_one)
    by exact (real_lt_eq_lt (real_plus real_zero X) (real_plus eta X) real_one
                Hstep1 (m3_ring_eta_kappa eta)).
  exact (real_eq_lt_lt (real_plus real_one (real_opp eta))
           (real_plus real_zero X) real_one
           (real_eq_trans (real_plus real_one (real_opp eta)) X (real_plus real_zero X)
              (real_eq_refl X)
              (real_eq_sym (real_plus real_zero X) X (kl_plus_zero_l X)))
           Hstep2).
Qed.

(* κ ≤ 1、0 ≤ y ⟹ κ·y ≤ y *)
Lemma m3_le_kappa_mul : forall kappa y : Real,
  real_le real_zero y -> real_le kappa real_one ->
  real_le (real_mult kappa y) y.
Proof.
  intros kappa y Hy0 Hk1.
  apply (kl_le_eq_r (real_mult kappa y) (real_mult real_one y) y).
  - exact (real_le_mult_compat_weak kappa real_one y Hy0 Hk1).
  - apply kl_mult_one_l.
Qed.

(* 0 ≤ c、a ≤ b ⟹ c·a ≤ c·b（左乘版） *)
Lemma m3_le_mult_compat_l : forall c a b : Real,
  real_le real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros c a b Hc Hab.
  apply (kl_le_eq_r (real_mult c a) (real_mult b c) (real_mult c b)).
  - apply (kl_le_eq_l (real_mult a c) (real_mult b c) (real_mult c a)).
    + exact (real_le_mult_compat_weak a b c Hc Hab).
    + apply real_mult_comm.
  - apply real_mult_comm.
Qed.

(* 环：a·(b+c) == a·b + a·c *)
Lemma m3_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 环：a·(b·c) == (a·b)·c *)
Lemma m3_ring_reassoc2 : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < x ⟹ 0 ≤ t·x *)
Lemma m3_nmul_nonneg : forall (k : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (m3_nmul k x).
Proof.
  intros k x Hx. induction k as [| k IH].
  - apply real_le_refl.
  - exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus x (m3_nmul k x)) real_zero
             (real_le_plus_compat real_zero x real_zero (m3_nmul k x)
                (kl_lt_le_bridge real_zero x Hx) IH)
             kl_zero_plus_zero).
Qed.

(* n ≠ 0 ⟹ 状态表非空 *)
Lemma m3_seq_nonnil : forall n : nat, n <> 0 -> m3_states n <> nil.
Proof.
  intros n Hn Hnil. unfold m3_states in Hnil.
  destruct n as [| m].
  - exact (Hn eq_refl).
  - simpl in Hnil. discriminate Hnil.
Qed.

(* 逐项正项的 list 和为正（配分函数正性核） *)
Lemma m3_interp_Z_pos2 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k e : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero
    (real_list_sum nat
       (fun i : nat => real_mult
          (real_pow_pos (q i) k (Hq i)) (real_pow_pos (r i) e (Hr i)))
       (m3_states n)).
Proof.
  intros n Hn q r k e Hq Hr.
  apply (real_list_sum_pos nat).
  - intro i.
    exact (real_mult_positive (real_pow_pos (q i) k (Hq i))
             (real_pow_pos (r i) e (Hr i))
             (cauchy_real_exp_pos (real_mult k (cw_log (q i) (Hq i))))
             (cauchy_real_exp_pos (real_mult e (cw_log (r i) (Hr i))))).
  - exact (m3_seq_nonnil n Hn).
Qed.

(* 同上，结论取 real_interp_Z 原生形态（供 pkg 的 sigT 组件直接对型） *)
Lemma m3_interp_Z_pos3 : forall (n : nat) (Hn : n <> 0) (q r : nat -> Real)
    (k : Real)
    (Hq : forall i : nat, real_lt real_zero (q i))
    (Hr : forall i : nat, real_lt real_zero (r i)),
  real_lt real_zero (real_interp_Z n q r k Hq Hr).
Proof.
  intros n Hn q r k Hq Hr.
  exact (m3_interp_Z_pos2 n Hn q r (real_plus real_one (real_opp k)) k Hq Hr).
Qed.

(* 单步更新逐点正性：π'(i) := (r(i)^{1−k}·p(i)^k)·inv Z > 0 *)
Definition m3_step_pos_pt (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp))
    (i : nat)
  : real_lt real_zero (real_step_next n r p k Hr Hp HZ i) :=
  real_mult_positive
    (real_mult (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
               (real_pow_pos (p i) k (Hp i)))
    (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
    (real_mult_positive
       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
       (real_pow_pos (p i) k (Hp i))
       (cauchy_real_exp_pos
          (real_mult (real_plus real_one (real_opp k)) (cw_log (r i) (Hr i))))
       (cauchy_real_exp_pos (real_mult k (cw_log (p i) (Hp i)))))
    (real_inv_pos_pos (real_interp_Z n r p k Hr Hp) HZ).

(* 单步更新归一化：Σ π' == inv Z·Z == 1（配分函数吸收） *)
Lemma m3_step_next_norm : forall (n : nat) (r p : nat -> Real) (k : Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (HZ : real_lt real_zero (real_interp_Z n r p k Hr Hp)),
  real_eq
    (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))
    real_one.
Proof.
  intros n r p k Hr Hp HZ.
  exact (real_eq_trans
           (real_list_sum nat (real_step_next n r p k Hr Hp HZ) (m3_states n))
           (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                      (real_list_sum nat
                         (fun i : nat => real_mult
                            (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
                            (real_pow_pos (p i) k (Hp i)))
                         (m3_states n)))
           real_one
           (real_list_sum_linear_r nat
              (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
              (fun i : nat => real_mult
                 (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
                 (real_pow_pos (p i) k (Hp i)))
              (m3_states n))
           (real_eq_trans
              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                         (real_list_sum nat
                            (fun i : nat => real_mult
                               (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
                               (real_pow_pos (p i) k (Hp i)))
                            (m3_states n)))
              (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                         (real_interp_Z n r p k Hr Hp))
              real_one
              (RealSetoid.real_eq_mult_compat
                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                 (real_list_sum nat
                    (fun i : nat => real_mult
                       (real_pow_pos (r i) (real_plus real_one (real_opp k)) (Hr i))
                       (real_pow_pos (p i) k (Hp i)))
                    (m3_states n))
                 (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                 (real_interp_Z n r p k Hr Hp)
                 (real_eq_refl (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))
                 (real_eq_refl (real_interp_Z n r p k Hr Hp)))
              (real_eq_trans
                 (real_mult (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                            (real_interp_Z n r p k Hr Hp))
                 (real_mult (real_interp_Z n r p k Hr Hp)
                            (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ))
                 real_one
                 (real_mult_comm (real_inv_pos (real_interp_Z n r p k Hr Hp) HZ)
                                 (real_interp_Z n r p k Hr Hp))
                 (real_inv_pos_correct (real_interp_Z n r p k Hr Hp) HZ)))).
Qed.

(* ========== 策略迭代序列（sigT 打包：策略+正性+配分函数正性+归一化） ========== *)

(* 迭代包类型：p := π_t 连同其逐点正性、下一步配分函数正性、归一化恒等 *)
Definition m3_pkg_type (n : nat) (r : nat -> Real) (eta : Real)
    (Hr : forall i : nat, real_lt real_zero (r i)) : Type :=
  { p : nat -> Real &
    { Hp : forall i : nat, real_lt real_zero (p i) &
      { HZ : real_lt real_zero (real_interp_Z n r p (m3_kappa eta) Hr Hp) &
        real_eq (real_list_sum nat p (m3_states n)) real_one } } }.

(* π_{t+1}(i) := real_step_next n r π_t (1−η)：几何插值策略更新
   π_{t+1}(i) := π*(i)^η·π_t(i)^{1−η}/Z_t。
   单 Fixpoint（对 t 结构递归），O 情形携带初值四件套，
   S 情形经 m3_step_pos_pt / m3_interp_Z_pos2 / m3_step_next_norm
   同步重建四件套。 *)
Fixpoint m3_pi_pkg (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) {struct t} : m3_pkg_type n r eta Hr :=
  match t with
  | Datatypes.O => existT _ p0 (existT _ Hp0 (existT _ HZ1 Hnorm0))
  | Datatypes.S t' =>
      let pkg := m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t' in
      let p := projT1 pkg in
      let Hp := projT1 (projT2 pkg) in
      let HZ := projT1 (projT2 (projT2 pkg)) in
      (existT _ (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
         (existT _ (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)
           (existT
              (fun HZ' : real_lt real_zero
                          (real_interp_Z n r
                             (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                             (m3_kappa eta) Hr
                             (fun i : nat =>
                                m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i)) =>
                 real_eq
                   (real_list_sum nat
                      (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                      (m3_states n))
                   real_one)
              (m3_interp_Z_pos3 n Hn r
                 (real_step_next n r p (m3_kappa eta) Hr Hp HZ)
                 (m3_kappa eta) Hr
                 (fun i : nat => m3_step_pos_pt n r p (m3_kappa eta) Hr Hp HZ i))
              (m3_step_next_norm n r p (m3_kappa eta) Hr Hp HZ)))
       : m3_pkg_type n r eta Hr)
  end.

(* 四投影：迭代策略序列 / 逐点正性 / 配分函数正性 / 归一化 *)
Definition m3_pi_seq (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) : nat -> Real :=
  projT1 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t).

Definition m3_pi_seq_pos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  forall i : nat,
    real_lt real_zero (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t i) :=
  fun i : nat => projT1 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) i.

Definition m3_pi_seq_Zpos (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_lt real_zero
    (real_interp_Z n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
       (m3_kappa eta) Hr (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)) :=
  projT1 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

Definition m3_pi_seq_norm (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (t : nat) :
  real_eq
    (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) (m3_states n))
    real_one :=
  projT2 (projT2 (projT2 (m3_pi_pkg n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).

(* ========== M3.1 前置：M2 换向单步几何收缩（eps 化 geom_step） ========== *)

(* 单步真几何率（根内 policy_iter_kl_geom_step 的 eps 化镜像）：
   KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + eps。
   即 UpStepKL 的 M2（real_step_kl_eta_bound_eps）在迭代序列第 t 步的
   直接实例化：p-槽 := r（π*），r-槽 := π_t，eta-槽 := κ := 1−η。 *)
Corollary real_iter_step_geom_eps :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       eps).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  exact (real_step_kl_eta_bound_eps n r
           (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
           (m3_kappa eta) Hr
           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
           Hnormr (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
           (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
           (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
           (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)
           eps Heps).
Qed.

(* ========== M3.1：单步向后 KL 递推（backward_kl_step_le 的 eps 化镜像） ========== *)
(* KL(π*‖π_{t+1}) ≤ (1−η)·KL(π*‖π_t) + KL(π_t‖π_{t+1}) + eps
   路线（对应根内 policy_iter_backward_kl_step_le 的「丢弃负项」）：
   M2 换向实例给 KL(π*‖π_{t+1}) ≤ (1−η)KL(π*‖π_t) + d（d := eps/2），
   Gibbs 下界给 0 ≤ KL(π_t‖π_{t+1}) + d，两式相加后对半预算吸收 eps。 *)
Theorem real_iter_kl_step :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
    (real_plus
       (real_mult (m3_kappa eta)
          (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)))
       (real_plus
          (m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
             (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
          eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1 t eps Heps.
  assert (HnormP : forall s : nat,
            real_eq
              (real_list_sum nat (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 s)
                 (m3_states n))
              real_one)
    by exact (m3_pi_seq_norm n p0 r eta Hn Hp0 Hr HZ1 Hnorm0).
  set (A := real_mult (m3_kappa eta)
              (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                 (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))).
  set (B := m3_kl_list n (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))).
  set (d := m3_half eps).
  apply (real_le_trans
           (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
              (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
           (real_plus (real_plus A d) (real_plus B d))
           (real_plus A (real_plus B eps))).
  - apply (real_le_trans
             (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)) Hr
                (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t)))
             (real_plus A d)
             (real_plus (real_plus A d) (real_plus B d))).
    + (* M2 换向实例：KL(π*‖π_{t+1}) ≤ κ·KL(π*‖π_t) + d *)
      exact (real_step_kl_eta_bound_eps n r
               (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_kappa eta) Hr
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               Hnormr (HnormP t)
               (m3_pi_seq_Zpos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
               (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
               (m3_kappa_pos eta Heta_lt1) (m3_kappa_le_one eta Heta_pos)
               d (m3_half_pos eps Heps)).
    + (* (A+d) ≤ (A+d) + (B+d)：Gibbs 下界 0 ≤ B + d *)
      exact (kl_le_eq_l (real_plus (real_plus A d) real_zero)
               (real_plus (real_plus A d) (real_plus B d))
               (real_plus A d)
               (real_le_plus_compat (real_plus A d) (real_plus A d)
                  real_zero (real_plus B d)
                  (real_le_refl (real_plus A d))
                  (real_gibbs_inequality_eps nat (m3_states n)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)
                     (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                     (HnormP t) (HnormP (Datatypes.S t)) d (m3_half_pos eps Heps)))
               (real_plus_zero (real_plus A d))).
  - (* eq 换形：(A+d)+(B+d) == A+(B+eps) *)
    exact (kl_eq_le_bridge (real_plus (real_plus A d) (real_plus B d))
             (real_plus A (real_plus B eps))
             (real_eq_trans (real_plus (real_plus A d) (real_plus B d))
             (real_plus (real_plus A B) (real_plus d d))
             (real_plus A (real_plus B eps))
             (real_plus_swap_mid A d B d)
             (real_eq_trans (real_plus (real_plus A B) (real_plus d d))
                (real_plus (real_plus A B) eps)
                (real_plus A (real_plus B eps))
                (RealSetoid.real_eq_plus_compat (real_plus A B) (real_plus d d)
                   (real_plus A B) eps
                   (real_eq_refl (real_plus A B))
                   (m3_half_double_eq eps))
                (real_eq_sym (real_plus A (real_plus B eps))
                   (real_plus (real_plus A B) eps)
                   (real_plus_assoc A B eps))))).
Qed.

(* ========== M3.2：真几何率迭代（geom_iter 的 eps 化镜像） ========== *)
(* KL(π*‖π_t) ≤ (1−η)^t·KL(π*‖π_0) + t·eps
   （根内 policy_iter_kl_geom_iter 的 eps 化镜像：单步收缩
     real_iter_step_geom_eps 对 t 归纳，误差按 t 步算术累积。） *)
Theorem real_iter_kl_geom :
  forall (n : nat) (p0 r : nat -> Real) (eta : Real) (Hn : n <> 0)
    (Hp0 : forall i : nat, real_lt real_zero (p0 i))
    (Hr : forall i : nat, real_lt real_zero (r i))
    (HZ1 : real_lt real_zero (real_interp_Z n r p0 (m3_kappa eta) Hr Hp0))
    (Hnorm0 : real_eq (real_list_sum nat p0 (m3_states n)) real_one)
    (Hnormr : real_eq (real_list_sum nat r (m3_states n)) real_one)
    (Heta_pos : real_lt real_zero eta)
    (Heta_lt1 : real_lt eta real_one),
  forall (t : nat) (eps : Real), real_lt real_zero eps ->
  real_le
    (m3_kl_list n r (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
       (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t))
    (real_plus
       (real_mult (m3_rpow (m3_kappa eta) t)
          (m3_kl_list n r p0 Hr Hp0))
       (m3_nmul t eps)).
Proof.
  intros n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 Hnormr Heta_pos Heta_lt1
         t eps Heps.
  induction t as [| t IH].
  - (* t = 0：κ^0 == 1、0·eps == 0，KL ≤ 1·KL + 0 == KL *)
    cbn [m3_rpow m3_nmul].
    apply kl_eq_le_bridge.
    apply (real_eq_sym
             (real_plus
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero)
             (m3_kl_list n r p0 Hr Hp0)).
    exact (real_eq_trans
             (real_plus (real_mult real_one (m3_kl_list n r p0 Hr Hp0))
                        real_zero)
             (real_plus (m3_kl_list n r p0 Hr Hp0) real_zero)
             (m3_kl_list n r p0 Hr Hp0)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one (m3_kl_list n r p0 Hr Hp0)) real_zero
                (m3_kl_list n r p0 Hr Hp0) real_zero
                (kl_mult_one_l (m3_kl_list n r p0 Hr Hp0))
                (real_eq_refl real_zero))
             (real_plus_zero (m3_kl_list n r p0 Hr Hp0))).
  - (* t = S t：单步收缩 + IH 单调放大 + κ 系数重排 + 误差累积 *)
    cbn [m3_rpow m3_nmul].
    pose proof (real_iter_step_geom_eps n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                  Hnormr Heta_pos Heta_lt1 t eps Heps) as Hstep.
    set (KL0 := m3_kl_list n r p0 Hr Hp0).
    set (KLt := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t) Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 t)).
    set (KLs := m3_kl_list n r
                  (m3_pi_seq n p0 r eta Hn Hp0 Hr HZ1 Hnorm0 (Datatypes.S t))
                  Hr
                  (m3_pi_seq_pos n p0 r eta Hn Hp0 Hr HZ1 Hnorm0
                     (Datatypes.S t))).
    set (Y := m3_nmul t eps).
    set (X := real_mult (m3_rpow (m3_kappa eta) t) KL0).
    (* κ·单调：0 ≤ κ、IH ⟹ κ·KL_t ≤ κ·(κ^t·KL0 + t·eps) *)
    assert (Hmono : real_le (real_mult (m3_kappa eta) KLt)
                            (real_mult (m3_kappa eta) (real_plus X Y))).
    { apply (m3_le_mult_compat_l (m3_kappa eta)).
      - exact (kl_lt_le_bridge real_zero (m3_kappa eta)
                 (m3_kappa_pos eta Heta_lt1)).
      - exact IH. }
    (* 单步链：KL_{t+1} ≤ κ·KL_t + eps ≤ κ·(κ^t·KL0 + Y) + eps *)
    assert (Hchain : real_le KLs
                       (real_plus (real_mult (m3_kappa eta) (real_plus X Y))
                          eps)).
    { apply (real_le_trans KLs (real_plus (real_mult (m3_kappa eta) KLt) eps)).
      - exact Hstep.
      - exact (real_le_plus_compat (real_mult (m3_kappa eta) KLt)
                  (real_mult (m3_kappa eta) (real_plus X Y)) eps eps
                  Hmono (real_le_refl eps)). }
    (* 终组装：κ·(X+Y)+eps ≤ (κ·κ^t)·KL0 + (Y+eps)（κ·Y ≤ Y） *)
    apply (real_le_trans KLs
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps))
             (real_plus
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                   KL0)
                (real_plus eps Y))).
    + apply (kl_le_eq_r _ (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)).
      * exact Hchain.
      * exact (real_eq_trans
                 (real_plus (real_mult (m3_kappa eta) (real_plus X Y)) eps)
                 (real_plus (real_plus (real_mult (m3_kappa eta) X)
                              (real_mult (m3_kappa eta) Y)) eps)
                 (real_plus
                    (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                       KL0)
                    (real_plus (real_mult (m3_kappa eta) Y) eps))
                 (RealSetoid.real_eq_plus_compat
                    (real_mult (m3_kappa eta) (real_plus X Y))
                    eps
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_mult (m3_kappa eta) Y))
                    eps
                    (m3_distrib_l (m3_kappa eta) X Y)
                    (real_eq_refl eps))
                 (real_eq_trans
                    (real_plus
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y)) eps)
                    (real_plus (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_plus
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps))
                    (real_eq_sym
                       (real_plus (real_mult (m3_kappa eta) X)
                          (real_plus (real_mult (m3_kappa eta) Y) eps))
                       (real_plus
                          (real_plus (real_mult (m3_kappa eta) X)
                             (real_mult (m3_kappa eta) Y)) eps)
                       (real_plus_assoc (real_mult (m3_kappa eta) X)
                          (real_mult (m3_kappa eta) Y) eps))
                    (RealSetoid.real_eq_plus_compat
                       (real_mult (m3_kappa eta) X)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t))
                          KL0)
                       (real_plus (real_mult (m3_kappa eta) Y) eps)
                       (m3_ring_reassoc2 (m3_kappa eta) (m3_rpow (m3_kappa eta) t) KL0)
                       (real_eq_refl (real_plus (real_mult (m3_kappa eta) Y) eps))))).
    + exact (real_le_plus_compat
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0)
                (real_plus (real_mult (m3_kappa eta) Y) eps)
                (real_plus eps Y)
                (real_le_refl
                   (real_mult (real_mult (m3_kappa eta) (m3_rpow (m3_kappa eta) t)) KL0))
                (kl_le_eq_r
                   (real_plus (real_mult (m3_kappa eta) Y) eps)
                   (real_plus Y eps)
                   (real_plus eps Y)
                   (real_le_plus_compat (real_mult (m3_kappa eta) Y) Y eps eps
                      (m3_le_kappa_mul (m3_kappa eta) Y
                         (m3_nmul_nonneg t eps Heps)
                         (m3_kappa_le_one eta Heta_pos))
                      (real_le_refl eps))
                   (real_plus_comm Y eps))).
Qed.

(* ---------- UpRecast ---------- *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Module UpRecastISO.

Section RecastBody.

Local Notation S := Datatypes.S (only parsing).
Local Notation O := Datatypes.O (only parsing).

(* ===================================================================== *)
(* UpRecast.v — GRM 再铸链 Coq 落地：use 事件账本 + survive 幸存扫描 +       *)
(*              recast 再铸 + 未桥尾义务（可再入）+ 摩擦计量                 *)
(*                                                                       *)
(* 二轮圆桌 Q3 立项（2 票：席 2/席 3，投票理由：全场最干净结构性抢救 +       *)
(* 首尾咬合）。设计出处：                                                  *)
(*   ROUNDTABLE2.md 席 1 段落（GRM 签名草稿 + v2 终稿）；                   *)
(*   ROUNDTABLE2.md 席 1 实验区【抢救一：WPM → GRM 账本上的再铸链】；        *)
(*   成果存档/圆桌会议/排队席位方案-二轮成果Coq化-20260907.md Q3 条目。       *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；语句零 Prop（Set/Type 层 cwe_tid 恒等型 + cwe_nle 序型  *)
(* + pick 双分支判定，Rocq 9.1 sumbool 参数为 Prop 不可载 Type 见件 2 注）；    *)
(* stdlib only；纯构造性。                                                  *)
(*                                                                       *)
(* 五件：                                                                 *)
(*   件 1  use 事件账本（append-only 账本推进 + 逐字段 use 账户单调）         *)
(*   件 2  survive 幸存扫描（长度分割守恒 + 幸存者纯净 + bool 判定全覆盖）     *)
(*   件 3  recast 再铸（普查不增 + 义务不灭 + 总账平衡 + 等级质量守恒）        *)
(*   件 4  未桥尾义务可再入（rebridge 清账再入 + recast∘rebridge 循环咬合     *)
(*         + 任意长再铸链 chain 总账守恒）                                  *)
(*   件 5  摩擦计量（每轮精确差值 +1/+2 + 全链单调 + 循环严格推进）            *)
(*                                                                       *)
(* 定稿决策（原设计未定稿处，按「结构最干净 + 首尾咬合」定稿）：               *)
(*   D1  载体细化：fid=tier=nat、evid=Z（证据强度取 |ev| 的 nat 编码）；       *)
(*       Cert = 普查 census + 未桥义务账 obls + 计量 meter 三分账，           *)
(*       义务账户独立成账（原草稿义务混在普查标记里），首尾咬合更干净。         *)
(*   D2  行内测验语义：passes f ev c := find 普查读出 f 的等级 t，             *)
(*       t <= |ev| 判通过（bool 全判定）；通过档计量 +1 不动普查，             *)
(*       击穿档走 survive 扫描降级再铸（计量 +1+1）。                         *)
(*   D3  击穿粒度：survive 扫描按字段整体过滤，f 的全部条目整体降级，           *)
(*       义务账逐条携带原等级（verbatim 转移）——等级质量守恒因此成立。         *)
(*   D4  再入语义：rebridge c f 把义务账中 f 的全部条目移回普查尾部的，        *)
(*       同一 keepF/hitF 判定面复用于普查与义务两账（一台机器两本账）；        *)
(*       recast∘rebridge 循环严格增摩擦 + 总账守恒，即可无限再入的链。         *)
(*   D5  v2 耦合谱系账的归并机制不在本件（属上游普查结构假设，E1 反例          *)
(*       已证字段独立公理不可依赖）；本件在任意普查上建账，耦合谱系可作为      *)
(*       上游换代挂入，recast 链接口不变——与 Q3 条目「未定稿细节自行定稿」    *)
(*       一致，诚实声明而非降级。                                           *)
(* ===================================================================== *)

Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建：cwe_tid 恒等型 / cwe_nle 序型 / 判定存活工具（内联自 UpPLA §0）      *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive cwe_tid (A : Type) : A -> A -> Type := cwe_tid_refl : forall x : A, cwe_tid A x x.

Definition cwe_tid_sym (A : Type) (x y : A) (H : cwe_tid A x y) : cwe_tid A y x :=
  match H in cwe_tid _ a b return cwe_tid _ b a with
  | cwe_tid_refl _ a0 => @cwe_tid_refl _ a0
  end.

Definition cwe_tid_trans (A : Type) (x y z : A) (H1 : cwe_tid A x y) (H2 : cwe_tid A y z) :
  cwe_tid A x z :=
  match H1 in cwe_tid _ a b return cwe_tid _ b z -> cwe_tid _ a z with
  | cwe_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition cwe_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : cwe_tid A x y) :
  cwe_tid B (f x) (f y) :=
  match H in cwe_tid _ a b return cwe_tid B (f a) (f b) with
  | cwe_tid_refl _ a0 => @cwe_tid_refl _ (f a0)
  end.

(* Set 层自然数序型（k < m 编码为 cwe_nle (S k) m） *)
Inductive cwe_nle (n : nat) : nat -> Set :=
| cwe_nle_n : cwe_nle n n
| cwe_nle_S : forall m : nat, cwe_nle n m -> cwe_nle n (S m).

Ltac tidE H :=
  pose proof (match H in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as HE.

(* bool 恒等矛盾关闭器：H1 : cwe_tid bool X true、H2 : cwe_tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

Lemma cwe_leb_refl_tid : forall a : nat, cwe_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply cwe_tid_refl.
Qed.

Lemma cwe_leb_S : forall a m : nat,
  cwe_tid bool (Nat.leb a m) true -> cwe_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply cwe_tid_refl.
    + change (cwe_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply cwe_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint cwe_nle_lebF (a b : nat) (H : cwe_nle a b) {struct H} :
  cwe_tid bool (Nat.leb a b) true :=
  match H as H0 in cwe_nle _ bb
  return cwe_tid bool (Nat.leb a bb) true with
  | cwe_nle_n _ => cwe_leb_refl_tid a
  | cwe_nle_S _ m H1 => cwe_leb_S a m (cwe_nle_lebF a m H1)
  end.

Definition cwe_nle_leb (b a : nat) (H : cwe_nle a b) : cwe_tid bool (Nat.leb a b) true :=
  cwe_nle_lebF a b H.

(* cwe_nle -> nat ≤ 提取（仅证明内部推理用） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (cwe_nle_leb _ _ H) in cwe_tid _ x y return x = y with
        | cwe_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma cwe_nle_SS : forall a b : nat, cwe_nle a b -> cwe_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply cwe_nle_n.
  - apply cwe_nle_S. exact IH.
Qed.

Lemma cwe_nle_0 : forall m : nat, cwe_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply cwe_nle_n.
  - apply cwe_nle_S. exact IH.
Qed.

Lemma cwe_nle_of_leb : forall b a : nat,
  cwe_tid bool (Nat.leb a b) true -> cwe_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply cwe_nle_n.
    + change (cwe_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply cwe_nle_0.
    + apply cwe_nle_SS. exact (IB a1 H).
Qed.

Lemma cwe_nle_trans : forall a b c : nat, cwe_nle a b -> cwe_nle b c -> cwe_nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply cwe_nle_S. exact IH.
Qed.

(* cwe_nle (S a) (S b) -> cwe_nle a b *)
Lemma cwe_nle_pred : forall a b : nat, cwe_nle (S a) (S b) -> cwe_nle a b.
Proof.
  intros a b H. apply cwe_nle_of_leb.
  exact (cwe_nle_leb (S b) (S a) H).
Qed.

Lemma cwe_nle_add_r : forall a b : nat, cwe_nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply cwe_nle_0.
  - exact (cwe_nle_SS a1 (a1 + b) (IH b)).
Qed.

(* ---- 本件新增基建 ---- *)

Lemma nle_S_diag : forall a : nat, cwe_nle a (S a).
Proof.
  induction a as [| a IH].
  - apply cwe_nle_0.
  - apply cwe_nle_SS. exact IH.
Qed.

Lemma nle_add_r_any : forall a b c : nat, cwe_nle a b -> cwe_nle (a + c) (b + c).
Proof.
  intros a b c H. induction H as [| m H IH].
  - apply cwe_nle_n.
  - replace (Nat.add (S m) c) with (S (Nat.add m c)) by reflexivity.
    apply cwe_nle_S. exact IH.
Qed.

Lemma nle_add_l_any : forall a b c : nat, cwe_nle b c -> cwe_nle (a + b) (a + c).
Proof.
  intros a b c H. induction a as [| a IH].
  - exact H.
  - apply cwe_nle_SS. exact IH.
Qed.

(* nat/bool 层 eq -> cwe_tid 桥（证明内部收尾用） *)
Lemma tid_nat_eq : forall a b : nat, a = b -> cwe_tid nat a b.
Proof.
  intros a b H. rewrite H. apply cwe_tid_refl.
Qed.

Lemma tid_bool_eq : forall x y : bool, x = y -> cwe_tid bool x y.
Proof.
  intros x y H. rewrite H. apply cwe_tid_refl.
Qed.

(* ---- 通用列表算术（自证防 stdlib 改名漂移） ---- *)

Lemma rc_len_app : forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = Nat.add (length l1) (length l2).
Proof.
  intros A l1. induction l1 as [| a l1 IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rc_filter_partition_len : forall (A : Type) (g : A -> bool) (l : list A),
  length l = Nat.add (length (filter g l)) (length (filter (fun x => negb (g x)) l)).
Proof.
  intros A g l. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (g a); simpl; lia.
Qed.

Lemma rc_filter_app : forall (A : Type) (g : A -> bool) (l1 l2 : list A),
  filter g (l1 ++ l2) = filter g l1 ++ filter g l2.
Proof.
  intros A g l1. induction l1 as [| a l1 IH]; intros l2; simpl.
  - reflexivity.
  - destruct (g a); simpl; rewrite IH; reflexivity.
Qed.

Lemma rc_filter_filter_len : forall (A : Type) (g : A -> bool) (l : list A),
  length (filter g (filter g l)) = length (filter g l).
Proof.
  intros A g l. induction l as [| a l IH].
  - reflexivity.
  - destruct (g a) eqn:Ega.
    + simpl. rewrite ?Ega. simpl. rewrite ?Ega. simpl. rewrite IH. reflexivity.
    + simpl. rewrite ?Ega. simpl. rewrite ?Ega. simpl. exact IH.
Qed.

Lemma rc_existsb_filter_neg : forall (A : Type) (g : A -> bool) (l : list A),
  existsb g (filter (fun x => negb (g x)) l) = false.
Proof.
  intros A g l. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (g a) eqn:Ega.
    + cbn [existsb negb]. exact IH.
    + cbn [existsb negb]. rewrite ?Ega. simpl. exact IH.
Qed.

Lemma rc_existsb_filter_id : forall (A : Type) (g : A -> bool) (l : list A),
  existsb g (filter g l) = existsb g l.
Proof.
  intros A g l. induction l as [| a l IH].
  - reflexivity.
  - change (existsb g (filter g (a :: l)))
      with (existsb g (if g a then a :: filter g l else filter g l)).
    change (existsb g (a :: l)) with (orb (g a) (existsb g l)).
    destruct (g a) eqn:Ega.
    + simpl. rewrite Ega. reflexivity.
    + exact IH.
Qed.

(* ===================================================================== *)
(* 件 1. use 事件账本：append-only 账本 + 逐字段行使账户                      *)
(* ===================================================================== *)

Definition fid : Set := nat.
Definition tier : Set := nat.
Definition evid : Set := Z.

Inductive evt : Set := use : fid -> evid -> evt.

Record meter : Set := mkM { m_ev : nat; m_rc : nat }.

Record Cert : Set := mkC {
  census : list (fid * tier);   (* 幸存普查：字段 × 等级 *)
  obls   : list (fid * tier);   (* 未桥尾义务账：被击穿字段 × 失守等级     *)
  mtr    : meter                (* 摩擦计量：行使计数 + 再铸计数           *)
}.

(* 账本推进：事件只追加，历史永不改写 *)
Definition ledger_step (l : list evt) (e : evt) : list evt := l ++ [e].

(* 字段 f 的行使判定面（账本逐事件的分类 bool） *)
Definition is_use_f (f : fid) (e : evt) : bool :=
  match e with use g _ => Nat.eqb f g end.

(* 字段 f 的 use 行使账户：账本上对该字段行使的次数 *)
Definition use_cnt (f : fid) (l : list evt) : nat :=
  length (filter (is_use_f f) l).

Theorem ledger_len_step : forall (l : list evt) (e : evt),
  cwe_tid nat (S (length l)) (length (ledger_step l e)).
Proof.
  intros l e. apply tid_nat_eq. unfold ledger_step. rewrite rc_len_app. simpl. lia.
Qed.

(* 账本推进守恒/单调：use 事件只增不减逐字段账户 *)
Theorem ledger_use_mono : forall (f : fid) (l : list evt) (e : evt),
  cwe_nle (use_cnt f l) (use_cnt f (ledger_step l e)).
Proof.
  intros f l. induction l as [| a l IH]; intros e.
  - apply cwe_nle_0.
  - destruct a as [g ev]. unfold use_cnt in *. simpl.
    destruct (Nat.eqb f g).
    + apply cwe_nle_SS. exact (IH e).
    + exact (IH e).
Qed.

(* ===================================================================== *)
(* 件 2. survive 幸存扫描：最大幸存子证书（字段集过滤）+ bool 判定全覆盖       *)
(* ===================================================================== *)

Definition fidb (f g : fid) : bool := Nat.eqb f g.

(* 幸存判定面：字段不等于被击穿字段则幸存 *)
Definition keepF (f : fid) (p : fid * tier) : bool := negb (fidb f (fst p)).
(* 击穿判定面：字段恰为被击穿字段 *)
Definition hitF (f : fid) (p : fid * tier) : bool := fidb f (fst p).

(* 最大幸存子证书：普查中剔除被击穿字段的全部条目 *)
Definition survive_scan (f : fid) (l : list (fid * tier)) : list (fid * tier) :=
  filter (keepF f) l.
(* 被击穿而降级的条目（与幸存扫描互补，同一判定面） *)
Definition pierced (f : fid) (l : list (fid * tier)) : list (fid * tier) :=
  filter (hitF f) l.

(* 字段在册性的 bool 判定（零 Prop 的 In 代用品） *)
Definition occurs (f : fid) (l : list (fid * tier)) : bool :=
  existsb (hitF f) l.

(* 扫描完备性之一：长度分割守恒——幸存 + 击穿 = 全普查，一枚不丢 *)
Theorem scan_partition_len : forall (f : fid) (l : list (fid * tier)),
  cwe_tid nat (length l)
           (Nat.add (length (survive_scan f l)) (length (pierced f l))).
Proof.
  intros f l. apply tid_nat_eq. unfold survive_scan, pierced.
  rewrite Nat.add_comm.
  exact (rc_filter_partition_len (fid * tier) (hitF f) l).
Qed.

(* 扫描完备性之二：幸存者纯净——幸存子证书不再含被击穿字段 *)
Theorem scan_survivor_pure : forall (f : fid) (l : list (fid * tier)),
  cwe_tid bool (occurs f (survive_scan f l)) false.
Proof.
  intros f l. apply tid_bool_eq. unfold occurs, survive_scan.
  exact (rc_existsb_filter_neg (fid * tier) (hitF f) l).
Qed.

(* 扫描完备性之三：判定全覆盖——击穿侧恰捕获全部在册条目 *)
Theorem scan_pierce_capture : forall (f : fid) (l : list (fid * tier)),
  cwe_tid bool (occurs f (pierced f l)) (occurs f l).
Proof.
  intros f l. apply tid_bool_eq. unfold occurs, pierced.
  exact (rc_existsb_filter_id (fid * tier) (hitF f) l).
Qed.

(* bool 判定全覆盖：在册性总判定器（Type 排序双分支，零 Prop）。              *)
(* 定稿决策：Rocq 9.1 的 sumbool 参数已改 (A B : Prop)，装不下 cwe_tid 的 Type    *)
(* 载荷，故自建 Type 排序双分支载体 pick（判定器语义不变：分支即判定结果）。   *)
Inductive pick (A B : Type) : Type := pick_l : A -> pick A B | pick_r : B -> pick A B.

Theorem occurs_dec : forall (f : fid) (l : list (fid * tier)),
  pick (cwe_tid bool (occurs f l) true) (cwe_tid bool (occurs f l) false).
Proof.
  intros f l. unfold occurs.
  destruct (existsb (hitF f) l).
  - apply pick_l. apply tid_bool_eq. reflexivity.
  - apply pick_r. apply tid_bool_eq. reflexivity.
Qed.

(* 幸存子证书规模不超原普查 *)
Theorem scan_scan_mono : forall (f : fid) (l : list (fid * tier)),
  cwe_nle (length (survive_scan f l)) (length l).
Proof.
  intros f l. pose proof (scan_partition_len f l) as HP. tidE HP.
  rewrite HE. apply cwe_nle_add_r.
Qed.

(* 等级质量：普查条目的等级总和 *)
Definition tsum (l : list (fid * tier)) : nat :=
  fold_right (fun p a => Nat.add (snd p) a) O l.

Lemma rc_tsum_app : forall (l1 l2 : list (fid * tier)),
  tsum (l1 ++ l2) = Nat.add (tsum l1) (tsum l2).
Proof.
  intros l1. unfold tsum. induction l1 as [| a l1 IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma rc_tsum_filter_partition : forall (g : fid * tier -> bool)
                                        (l : list (fid * tier)),
  tsum l = Nat.add (tsum (filter g l)) (tsum (filter (fun x => negb (g x)) l)).
Proof.
  intros g l. unfold tsum. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (g a); simpl; lia.
Qed.

(* 扫描完备性之四：等级质量分割守恒——幸存 + 击穿 = 原质量 *)
Lemma rc_tsum_scan : forall (f : fid) (l : list (fid * tier)),
  tsum l = Nat.add (tsum (survive_scan f l)) (tsum (pierced f l)).
Proof.
  intros f l. unfold survive_scan, pierced.
  rewrite Nat.add_comm.
  exact (rc_tsum_filter_partition (hitF f) l).
Qed.

(* ===================================================================== *)
(* 件 3. recast 再铸：行内测验（bool 判定）+ 降级 + 义务转移 + 计量差值        *)
(* ===================================================================== *)

(* 等级读出：普查上 find 出字段 f 的条目，读出其等级 *)
Definition level_at (f : fid) (l : list (fid * tier)) : option tier :=
  match find (hitF f) l with
  | Some p => Some (snd p)
  | None => None
  end.

(* 行内测验（可判定准入）：证据强度 |ev| 不低于字段等级 t 则通过；           *)
(* 无等级在册（已降级/未发行）则不通过。全 bool，零 Prop。                  *)
Definition passes (f : fid) (ev : evid) (c : Cert) : bool :=
  match level_at f (census c) with
  | Some t => Nat.leb t (Z.to_nat (Z.abs ev))
  | None => false
  end.

(* 再铸本体：按测验 bool 分档（recast_b 提出分支，recast 只做 iota 分发，     *)
(* 使全部定理可用 change 一步落入可重写形态）                               *)
Definition recast_b (c : Cert) (f : fid) (ev : evid) (b : bool) : Cert :=
  if b
  then mkC (census c) (obls c) (mkM (S (m_ev (mtr c))) (m_rc (mtr c)))
  else mkC (survive_scan f (census c))
           (obls c ++ pierced f (census c))
           (mkM (S (m_ev (mtr c))) (S (m_rc (mtr c)))).

(* 消费事件驱动的再铸：下游实例化即行使一次行内测验 *)
Definition recast (c : Cert) (e : evt) : Cert :=
  match e with
  | use f ev => recast_b c f ev (passes f ev c)
  end.

(* 总账：普查条目 + 义务条目（再铸链的不变量载体） *)
Definition total_acc (c : Cert) : nat :=
  Nat.add (length (census c)) (length (obls c)).

(* 再铸分档辅助：通过档普查恒等 *)
Theorem recast_pass_census : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev c) true ->
  cwe_tid (list (fid * tier)) (census c) (census (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. exact (cwe_tid_refl (list (fid * tier)) (census c)).
Qed.

(* 再铸分档辅助：通过档旧义务全保留（义务不灭半边） *)
Theorem recast_pass_obls : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev c) true ->
  cwe_tid (list (fid * tier)) (obls c) (obls (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. exact (cwe_tid_refl (list (fid * tier)) (obls c)).
Qed.

(* 再铸击穿档：普查缩减恰为被击穿条目（义务转移的来源侧） *)
Theorem recast_pierce_partition : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev c) false ->
  cwe_tid nat (length (census c))
           (Nat.add (length (census (recast c (use f ev))))
                    (length (pierced f (census c)))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. unfold recast_b. cbn [census].
  exact (scan_partition_len f (census c)).
Qed.

(* 再铸击穿档：新义务恰为降级条目（义务转移的去向侧；旧义务消⟹新义务生） *)
Theorem recast_pierce_obls_len : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev c) false ->
  cwe_tid nat (length (obls (recast c (use f ev))))
           (Nat.add (length (obls c)) (length (pierced f (census c)))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. unfold recast_b. cbn [obls].
  apply tid_nat_eq. rewrite rc_len_app. reflexivity.
Qed.

(* 普查单调：再铸永不增发普查条目 *)
Theorem recast_census_mono : forall (c : Cert) (e : evt),
  cwe_nle (length (census (recast c e))) (length (census c)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply cwe_nle_n.
  - exact (scan_scan_mono f (census c)).
Qed.

(* 义务单调：再铸永不销毁既有义务 *)
Theorem recast_obls_mono : forall (c : Cert) (e : evt),
  cwe_nle (length (obls c)) (length (obls (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply cwe_nle_n.
  - unfold recast_b. cbn [obls]. rewrite rc_len_app. apply cwe_nle_add_r.
Qed.

(* 义务转移封闭性·总账平衡：任意再铸后总账守恒（账户总账平衡） *)
Theorem acc_balance : forall (c : Cert) (e : evt),
  cwe_tid nat (total_acc c) (total_acc (recast c e)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply cwe_tid_refl.
  - apply tid_nat_eq. unfold total_acc, recast_b. cbn [census obls].
    rewrite rc_len_app.
    pose proof (scan_partition_len f (census c)) as HP. tidE HP.
    rewrite HE. lia.
Qed.

(* 义务转移封闭性·等级质量守恒：降级 verbatim 转账，质量分毫不差 *)
Theorem tier_balance : forall (c : Cert) (e : evt),
  cwe_tid nat (Nat.add (tsum (census c)) (tsum (obls c)))
           (Nat.add (tsum (census (recast c e))) (tsum (obls (recast c e)))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply cwe_tid_refl.
  - apply tid_nat_eq. unfold recast_b. cbn [census obls].
    rewrite rc_tsum_app.
    rewrite (rc_tsum_scan f (census c)).
    lia.
Qed.

(* ===================================================================== *)
(* 件 5（先行）. 摩擦计量：精确差值 + 单调                                   *)
(* ===================================================================== *)

(* 摩擦计量总值 = 行使计数 + 再铸计数 *)
Definition friction (c : Cert) : nat := Nat.add (m_ev (mtr c)) (m_rc (mtr c)).

(* 通过档精确差值：恰 +1（行使计数 +1，再铸计数不动） *)
Theorem friction_pass_step : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev c) true ->
  cwe_tid nat (S (friction c)) (friction (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. apply cwe_tid_refl.
Qed.

(* 击穿档精确差值：恰 +2（行使 +1、再铸 +1） *)
Theorem friction_pierce_step : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev c) false ->
  cwe_tid nat (S (S (friction c))) (friction (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. apply tid_nat_eq. unfold friction, recast_b. simpl. lia.
Qed.

(* 摩擦计量单调：任意再铸摩擦不减 *)
Theorem friction_mono : forall (c : Cert) (e : evt),
  cwe_nle (friction c) (friction (recast c e)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_add_r_any (m_ev (mtr c)) (S (m_ev (mtr c))) (m_rc (mtr c))
             (nle_S_diag (m_ev (mtr c)))).
  - exact (cwe_nle_trans (Nat.add (m_ev (mtr c)) (m_rc (mtr c)))
                     (Nat.add (S (m_ev (mtr c))) (m_rc (mtr c)))
                     (Nat.add (S (m_ev (mtr c))) (S (m_rc (mtr c))))
                     (nle_add_r_any (m_ev (mtr c)) (S (m_ev (mtr c)))
                        (m_rc (mtr c)) (nle_S_diag (m_ev (mtr c))))
                     (nle_add_l_any (S (m_ev (mtr c))) (m_rc (mtr c))
                        (S (m_rc (mtr c))) (nle_S_diag (m_rc (mtr c))))).
Qed.

(* 行使计数单调 *)
Theorem meter_ev_mono : forall (c : Cert) (e : evt),
  cwe_nle (m_ev (mtr c)) (m_ev (mtr (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_S_diag (m_ev (mtr c))).
  - exact (nle_S_diag (m_ev (mtr c))).
Qed.

(* 再铸计数单调 *)
Theorem meter_rc_mono : forall (c : Cert) (e : evt),
  cwe_nle (m_rc (mtr c)) (m_rc (mtr (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (cwe_nle_n (m_rc (mtr c))).
  - exact (nle_S_diag (m_rc (mtr c))).
Qed.

(* ===================================================================== *)
(* 件 4. 未桥尾义务可再入：rebridge 清账再入 + 循环咬合 + 任意长再铸链        *)
(* ===================================================================== *)

(* 再入：把义务账中 f 的全部条目移回普查尾部（同一判定面复用于两本账） *)
Definition rebridge (c : Cert) (f : fid) : Cert :=
  mkC (census c ++ pierced f (obls c)) (survive_scan f (obls c)) (mtr c).

(* 再入守恒之一：总账平衡 *)
Theorem rebridge_balance : forall (c : Cert) (f : fid),
  cwe_tid nat (total_acc c) (total_acc (rebridge c f)).
Proof.
  intros c f. apply tid_nat_eq. unfold total_acc, rebridge. cbn [census obls].
  rewrite rc_len_app.
  pose proof (scan_partition_len f (obls c)) as HP. tidE HP.
  rewrite HE. lia.
Qed.

(* 再入守恒之二：等级质量守恒 *)
Theorem rebridge_tier_balance : forall (c : Cert) (f : fid),
  cwe_tid nat (Nat.add (tsum (census c)) (tsum (obls c)))
           (Nat.add (tsum (census (rebridge c f))) (tsum (obls (rebridge c f)))).
Proof.
  intros c f. apply tid_nat_eq. unfold rebridge. cbn [census obls].
  rewrite rc_tsum_app.
  rewrite (rc_tsum_scan f (obls c)).
  lia.
Qed.

(* 再入清账：义务账中 f 的在册性清零（该字段义务全部清偿回普查） *)
Theorem rebridge_clears : forall (c : Cert) (f : fid),
  cwe_tid bool (occurs f (obls (rebridge c f))) false.
Proof.
  intros c f. apply tid_bool_eq. unfold rebridge, occurs. cbn [obls].
  unfold survive_scan.
  exact (rc_existsb_filter_neg (fid * tier) (hitF f) (obls c)).
Qed.

(* 义务字段计数：f 在账上的条目数 *)
Definition cnt (f : fid) (l : list (fid * tier)) : nat :=
  length (pierced f l).

(* 再入回补：普查上 f 的条目数 = 原普查条目 + 义务账条目（可再入的记账面） *)
Theorem rebridge_cnt_reentry : forall (c : Cert) (f : fid),
  cwe_tid nat (cnt f (census (rebridge c f)))
           (Nat.add (cnt f (census c)) (cnt f (obls c))).
Proof.
  intros c f. apply tid_nat_eq. unfold rebridge, cnt. cbn [census].
  unfold pierced. rewrite rc_filter_app. rewrite rc_len_app.
  rewrite (rc_filter_filter_len (fid * tier) (hitF f) (obls c)).
  reflexivity.
Qed.

(* 首尾咬合·循环总账平衡：rebridge 再入后任意再铸，总账仍守恒——           *)
(* 义务账（尾）回补普查（头），循环可无限再入                              *)
Theorem cycle_balance : forall (c : Cert) (f : fid) (e : evt),
  cwe_tid nat (total_acc c) (total_acc (recast (rebridge c f) e)).
Proof.
  intros c f e. apply cwe_tid_trans with (y := total_acc (rebridge c f)).
  - apply rebridge_balance.
  - apply acc_balance.
Qed.

(* 首尾咬合·循环严格推进：击穿再铸一轮摩擦精确 +2（链不死锁、单调递增） *)
Theorem cycle_friction_strict : forall (c : Cert) (f : fid) (ev : evid),
  cwe_tid bool (passes f ev (rebridge c f)) false ->
  cwe_tid nat (S (S (friction c))) (friction (recast (rebridge c f) (use f ev))).
Proof.
  intros c f ev H. exact (friction_pierce_step (rebridge c f) f ev H).
Qed.

(* 再铸链驱动器：n 轮燃料消费事件流（{struct n} 保证结构递归） *)
Fixpoint chain (n : nat) (c : Cert) (es : list evt) {struct n} : Cert :=
  match n with
  | O => c
  | S n' =>
      match es with
      | [] => c
      | e :: rest => chain n' (recast c e) rest
      end
  end.

(* 链守恒：任意长度再铸链总账平衡 *)
Theorem chain_balance : forall (n : nat) (c : Cert) (es : list evt),
  cwe_tid nat (total_acc c) (total_acc (chain n c es)).
Proof.
  intros n. induction n as [| n IH]; intros c es; simpl.
  - apply cwe_tid_refl.
  - destruct es as [| e rest].
    + apply cwe_tid_refl.
    + apply cwe_tid_trans with (y := total_acc (recast c e)).
      * apply acc_balance.
      * apply IH.
Qed.

(* 链单调：任意长度再铸链摩擦不减（计量沿链累计） *)
Theorem chain_friction_mono : forall (n : nat) (c : Cert) (es : list evt),
  cwe_nle (friction c) (friction (chain n c es)).
Proof.
  intros n. induction n as [| n IH]; intros c es; simpl.
  - apply cwe_nle_n.
  - destruct es as [| e rest].
    + apply cwe_nle_n.
    + apply cwe_nle_trans with (b := friction (recast c e)).
      * apply friction_mono.
      * apply IH.
Qed.

End RecastBody.

End UpRecastISO.

(* ---------- UpCLQuery ---------- *)
From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Module UpCLQueryISO.

Section CLQueryBody.

Local Notation S := Datatypes.S (only parsing).
Local Notation O := Datatypes.O (only parsing).

(* ===================================================================== *)
(* UpCLQuery.v — CL 2.0 分型拒答 Coq 落地：三类查询显式分型 + 结构性拒答      *)
(*              + 差表封闭律语法免疫                                        *)
(*                                                                       *)
(* 设计出处：ROUNDTABLE2 席 3 终稿（轮次 3）CL 2.0（2 票，席 5/6 投票理由：    *)
(*   Coq 落地路径全场最短）；排队席位方案-二轮成果Coq化-20260907.md Q4 条目。  *)
(*                                                                       *)
(* 三组件：                                                                *)
(*   件 1  三类查询显式分型 qtype：[内]QIN 平移不变 / [值]QVAL 价值 /          *)
(*         [锚]QANC 绝对；可判定准入谓词（sumbool 三分派定义 bool 准入，       *)
(*         *_eq 引理给直读形式；正确性 iffT 定理：准入 ⟺ sigT 凭证）。        *)
(*   件 2  结构性拒答：qans = qans_val Z | qans_rej misscred——拒答是显式      *)
(*         构造，缺失凭证型标 misscred 显式枚举（缺在册 MC_RANGE / 缺头券      *)
(*         MC_VSLOT / 缺锚闭 MC_ANCH）；qdc 总分派 + qdc_spec +              *)
(*         qrej_admit_false + 券一次性（val_fresh_answer / val_burn_reject）。*)
(*   件 3  差表封闭律语法免疫：dtab 归纳型，封闭律 dsub_cocycle 对一切         *)
(*         d : dtab 无前提成立（破律差表在语法层不可写出——构造子封闭）；       *)
(*         gauge shift 下 [内]类裁决平移不变（qin_gauge_invariant），绝对读出  *)
(*         恰平移 c（pot_shift_moves）——语言中无平移不变的绝对读出通道。       *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；语句零 Prop：等式用 cwe_tid、序用 cwe_nle、            *)
(* 存在用 sigT、分支用 sumbool / bool+cwe_tid、⟺ 用 iffT（Set 层双函数记录）。   *)
(* 纪律：纯构造性、无任何公理式出口、stdlib only、全链可提取。                 *)
(* 定稿决策（未定稿细节按「落地最短+判定天然」自定，见交付报告）：             *)
(*   差量域取 Z（Q 的整数格，判定天然）；头元规范 h=0 固定（pot i = 差 i 0）；  *)
(*   头券 = 单槽 option (nat*Z)（指标+熔合绝对量），答一次即焚；               *)
(*   锚义务列 = acol 归纳型（锚闭合事件 acolS），准入 = aread 命中。           *)
(* ===================================================================== *)


Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建（自 UpPLA.v 内联：cwe_tid 恒等型 + cwe_nle 序型 + 判定工具）          *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive cwe_tid (A : Type) : A -> A -> Type := cwe_tid_refl : forall x : A, cwe_tid A x x.

Definition cwe_tid_sym (A : Type) (x y : A) (H : cwe_tid A x y) : cwe_tid A y x :=
  match H in cwe_tid _ a b return cwe_tid _ b a with
  | cwe_tid_refl _ a0 => @cwe_tid_refl _ a0
  end.

Definition cwe_tid_trans (A : Type) (x y z : A) (H1 : cwe_tid A x y) (H2 : cwe_tid A y z) :
  cwe_tid A x z :=
  match H1 in cwe_tid _ a b return cwe_tid _ b z -> cwe_tid _ a z with
  | cwe_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition cwe_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : cwe_tid A x y) :
  cwe_tid B (f x) (f y) :=
  match H in cwe_tid _ a b return cwe_tid B (f a) (f b) with
  | cwe_tid_refl _ a0 => @cwe_tid_refl _ (f a0)
  end.

(* 从 cwe_tid 提取定义等式（仅证明内部推理用，命名受控） *)
Ltac tidQ H E :=
  pose proof (match H in cwe_tid _ a b return a = b with cwe_tid_refl _ _ => eq_refl end) as E.

(* x = y -> cwe_tid A x y（定义等式反灌回恒等型） *)
Lemma cwe_tid_eq : forall (A : Type) (x y : A), x = y -> cwe_tid A x y.
Proof.
  intros A x y H. rewrite H. apply cwe_tid_refl.
Defined.

(* Set 层自然数序型（k ≤ m 编码为 cwe_nle k m） *)
Inductive cwe_nle (n : nat) : nat -> Set :=
| cwe_nle_n : cwe_nle n n
| cwe_nle_S : forall m : nat, cwe_nle n m -> cwe_nle n (S m).

Lemma cwe_leb_refl_tid : forall a : nat, cwe_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply cwe_tid_refl.
Qed.

Lemma cwe_leb_S : forall a m : nat,
  cwe_tid bool (Nat.leb a m) true -> cwe_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply cwe_tid_refl.
    + change (cwe_tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply cwe_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint cwe_nle_lebF (a b : nat) (H : cwe_nle a b) {struct H} :
  cwe_tid bool (Nat.leb a b) true :=
  match H as H0 in cwe_nle _ bb
  return cwe_tid bool (Nat.leb a bb) true with
  | cwe_nle_n _ => cwe_leb_refl_tid a
  | cwe_nle_S _ m H1 => cwe_leb_S a m (cwe_nle_lebF a m H1)
  end.

Definition cwe_nle_leb (b a : nat) (H : cwe_nle a b) : cwe_tid bool (Nat.leb a b) true :=
  cwe_nle_lebF a b H.

(* cwe_nle -> nat ≤ 提取（仅证明内部推理用） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (cwe_nle_leb _ _ H) in cwe_tid _ x y return x = y with
        | cwe_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma cwe_nle_0 : forall m : nat, cwe_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply cwe_nle_n.
  - apply cwe_nle_S. exact IH.
Qed.

Lemma cwe_nle_SS : forall a b : nat, cwe_nle a b -> cwe_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply cwe_nle_n.
  - apply cwe_nle_S. exact IH.
Qed.

(* cwe_nle -> leb = true 反向桥 *)
Lemma cwe_nle_of_leb : forall b a : nat,
  cwe_tid bool (Nat.leb a b) true -> cwe_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply cwe_nle_n.
    + change (cwe_tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply cwe_nle_S. apply cwe_nle_0.
    + exact (cwe_nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ -> cwe_tid bool (leb) true 桥 *)
Lemma cwe_lebT : forall a b : nat, (a <= b)%nat -> cwe_tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply cwe_tid_refl.
Qed.

(* cwe_nle (S m) O 荒谬件（索引不交配的空消去，合法关闭任意 Type 目标） *)
Lemma nle_S_absurd : forall (m : nat) (P : Type), cwe_nle (S m) O -> P.
Proof.
  intros m P H. inversion H.
Qed.

(* Set 层 ⟺ 载体：双函数记录（语句零 Prop 的当且仅当） *)
Record iffT (A B : Type) : Type := mkIffT
  { iffT_fw : A -> B
  ; iffT_bw : B -> A }.

(* ===================================================================== *)
(* 1. 差表 dtab：归纳构造的恒差账（语法免疫载体）                              *)
(*    封闭律 差 i j + 差 j k == 差 i k 对一切 dtab 无前提成立——               *)
(*    不存在能写出破律差表的构造子。                                          *)
(* ===================================================================== *)

Inductive dtab : Set :=
| dtab1 (c : Z)                    (* 单指标账：指标 0（头元），gauge 值 c    *)
| dtabSnoc (d : dtab) (w : Z).     (* 入元：新指标 S (dlen d)，其与头元差 w   *)

(* 账内指标数：合法指标域 0 .. dlen d *)
Fixpoint dlen (d : dtab) : nat :=
  match d with
  | dtab1 _ => O
  | dtabSnoc d0 _ => S (dlen d0)
  end.

(* 头元规范 h=0 下的势读数：pot i = 差 i 0（由构造累积，绝非物质化总量） *)
Fixpoint pot (d : dtab) (i : nat) : Z :=
  match d with
  | dtab1 c => if Nat.eqb i O then c else 0
  | dtabSnoc d0 w => if Nat.eqb i (S (dlen d0)) then w else pot d0 i
  end.

(* 差 i j（唯一导出的 [内]类观测量） *)
Definition dsub (d : dtab) (i j : nat) : Z := pot d i - pot d j.

(* 件 3 核心定理：环形封闭律对一切 dtab 构造性成立（无任何前提） *)
Theorem dsub_cocycle : forall (d : dtab) (i j k : nat),
  cwe_tid Z (dsub d i j + dsub d j k) (dsub d i k).
Proof.
  intros d i j k. unfold dsub.
  apply (cwe_tid_eq Z (pot d i - pot d j + (pot d j - pot d k)) (pot d i - pot d k)).
  ring.
Qed.

(* gauge 平移：整表势读数加 c（换头元规范的语法操作） *)
Fixpoint dshift (d : dtab) (c : Z) : dtab :=
  match d with
  | dtab1 c0 => dtab1 (c0 + c)
  | dtabSnoc d0 w => dtabSnoc (dshift d0 c) (w + c)
  end.

Lemma dlen_shift : forall (d : dtab) (c : Z), cwe_tid nat (dlen (dshift d c)) (dlen d).
Proof.
  intros d c. induction d as [c0 | d0 IH w].
  - simpl. apply cwe_tid_refl.
  - simpl. tidQ IH Edl. rewrite Edl. apply cwe_tid_refl.
Qed.

(* 件 3 对照定理：绝对势读数在 gauge 平移下恰移动 c（语言无平移不变的绝对读出） *)
Theorem pot_shift_moves : forall (d : dtab) (c : Z) (i : nat),
  cwe_nle i (dlen d) -> cwe_tid Z (pot (dshift d c) i) (pot d i + c).
Proof.
  intros d c i. induction d as [c0 | d0 IH w].
  - intros Hn. destruct i as [| i1].
    + simpl. apply cwe_tid_refl.
    + exact (nle_S_absurd i1 _ Hn).
  - intros Hn. simpl in Hn.
    pose proof (dlen_shift d0 c) as DL. tidQ DL Edl.
    simpl. rewrite Edl.
    destruct (Nat.eqb i (S (dlen d0))) eqn:E.
    + apply cwe_tid_refl.
    + apply IH. apply cwe_nle_of_leb. apply cwe_lebT.
      apply Nat.eqb_neq in E. nleP Hn. lia.
Qed.

(* [内]类差值读数 gauge 不变（合法指标域内） *)
Theorem dsub_shift_invariant : forall (d : dtab) (c : Z) (i j : nat),
  cwe_nle i (dlen d) -> cwe_nle j (dlen d) ->
  cwe_tid Z (dsub (dshift d c) i j) (dsub d i j).
Proof.
  intros d c i j Hi Hj. unfold dsub.
  pose proof (pot_shift_moves d c i Hi) as T1. tidQ T1 E1.
  pose proof (pot_shift_moves d c j Hj) as T2. tidQ T2 E2.
  apply (cwe_tid_eq Z (pot (dshift d c) i - pot (dshift d c) j) (pot d i - pot d j)).
  rewrite E1, E2. ring.
Qed.

(* ===================================================================== *)
(* 2. 锚义务已闭列 acol（[锚]类凭证载体：锚闭合事件显式归纳）                    *)
(* ===================================================================== *)

Inductive acol : Set :=
| acol0                          (* 空列：无任何已闭锚义务 *)
| acolS (a : acol) (i : nat) (c : Z).  (* 锚闭合事件：指标 i 外锚至绝对值 c *)

(* 锚读数：该指标最近一次闭合记录的绝对值；未闭 = None *)
Fixpoint aread (i : nat) (a : acol) : option Z :=
  match a with
  | acol0 => None
  | acolS a0 j c => if Nat.eqb i j then Some c else aread i a0
  end.

(* ===================================================================== *)
(* 3. 件 1：三类查询显式分型 qtype + 缺失凭证型标 misscred + 答型 qans          *)
(* ===================================================================== *)

(* 三类查询：[内]平移不变 / [值]价值 / [锚]绝对——语法上只有这三个构造子，
   任何混类提问（例如用 [内]类语法问绝对水平）不可写出。 *)
Inductive qtype : Set :=
| QIN (i j : nat)            (* [内] 平移不变类：问差 i j                    *)
| QVAL (i : nat)             (* [值] 价值类：问指标 i 的绝对量（耗头券）       *)
| QANC (i : nat) (a : Z).    (* [锚] 绝对类：问 i 的绝对水平对锚 a 的对齐差    *)

(* 缺失凭证型标：拒答值携带"缺哪种凭证"的结构信息（显式枚举） *)
Inductive misscred : Set :=
| MC_RANGE (i : nat)   (* 缺在册凭证：指标 i 未入账（0 .. dlen 之外） *)
| MC_VSLOT             (* 缺头券：单槽价值凭证缺席或已焚              *)
| MC_ANCH (i : nat).   (* 缺锚闭凭证：指标 i 无已闭锚义务             *)

(* 答型：左支 = 答值（显式构造），右支 = 结构性拒答（携缺失凭证型标）。
   拒答不是失败：qans_rej 是 qans 的一等构造子。 *)
Inductive qans : Set :=
| qans_val (z : Z)
| qans_rej (mc : misscred).

(* 答型→bool 判读（拒答诚实性定理用） *)
Definition qans_isans (r : qans) : bool :=
  match r with
  | qans_val _ => true
  | qans_rej _ => false
  end.

Definition tid_qans_val (z1 z2 : Z) (H : cwe_tid Z z1 z2) :
  cwe_tid qans (qans_val z1) (qans_val z2) :=
  cwe_tid_cong (@qans_val) z1 z2 H.

(* ===================================================================== *)
(* 4. 件 1：可判定准入谓词——三分派（sdec：sumbool 的信息性凭证版）             *)
(*    三分派 left 支携 Set 层凭证（stdlib sumbool 两支限 Prop，不可用）；        *)
(*    bool 准入取直读定义，与三分派经凭证型刻画互通（见下与 *_correct）。        *)
(* ===================================================================== *)

(* Set 层判定和（sumbool 的信息性凭证版：stdlib sumbool 两支限 Prop，
   无法携带 Set 层凭证，故自造同构三分派型；left/right 支均可携信息性凭证。
   与 option/sigT 同居 Type 层——全链信息性、可提取、零 Prop。） *)
Inductive sdec (A B : Type) : Type :=
| sdec_l (a : A)
| sdec_r (b : B).

(* nat 序的三分派：left = cwe_nle 凭证，right = leb=false 的 cwe_tid 证据
   （判定本体走全量化引理，避免 destruct 污染目标型中的 scrutinee） *)
Lemma nle_dc_gen : forall (p : bool) (a b : nat),
  p = Nat.leb a b -> sdec (cwe_nle a b) (cwe_tid bool (Nat.leb a b) false).
Proof.
  intros p a b E. destruct p as [] eqn:Ep.
  - apply sdec_l. exact (cwe_nle_of_leb b a (cwe_tid_eq bool (Nat.leb a b) true (eq_sym E))).
  - apply sdec_r. exact (cwe_tid_eq bool (Nat.leb a b) false (eq_sym E)).
Defined.

Definition nle_dc (a b : nat) : sdec (cwe_nle a b) (cwe_tid bool (Nat.leb a b) false) :=
  nle_dc_gen (Nat.leb a b) a b eq_refl.

(* [内]类准入三分派：left = 双在册 cwe_nle 凭证；right = 缺在册型标 *)
Definition qin_dc (d : dtab) (i j : nat)
  : sdec (prod (cwe_nle i (dlen d)) (cwe_nle j (dlen d))) misscred.
Proof.
  destruct (nle_dc i (dlen d)) as [Ha | Ha].
  - destruct (nle_dc j (dlen d)) as [Hb | Hb].
    + apply sdec_l. split; assumption.
    + apply sdec_r. apply (MC_RANGE j).
  - apply sdec_r. apply (MC_RANGE i).
Defined.

Definition qin_ok (d : dtab) (i j : nat) : bool :=
  Nat.leb i (dlen d) && Nat.leb j (dlen d).

(* [值]类准入三分派：left = 头券凭证（sigT 携券面绝对量）；right = 缺头券 *)
Definition qval_dc (v : option (nat * Z)) (i : nat)
  : sdec (sigT (fun w : Z => cwe_tid (option (nat * Z)) (Some (i, w)) v)) misscred.
Proof.
  destruct v as [[h w] |] eqn:Ev.
  - destruct (Nat.eqb h i) eqn:Eh.
    + apply sdec_l. apply (existT _ w).
      apply Nat.eqb_eq in Eh.
      exact (cwe_tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
               (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
    + apply sdec_r. apply MC_VSLOT.
  - apply sdec_r. apply MC_VSLOT.
Defined.

Definition qval_ok (v : option (nat * Z)) (i : nat) : bool :=
  match v with Some p => Nat.eqb (fst p) i | None => false end.

(* 头券券面绝对量读出 *)
Definition vs_val (v : option (nat * Z)) : Z :=
  match v with Some p => snd p | None => 0 end.

(* [锚]类准入三分派：left = 锚闭凭证（sigT 携锚面绝对量）；right = 缺锚闭 *)
Definition qanc_dc (a : acol) (i : nat)
  : sdec (sigT (fun c : Z => cwe_tid (option Z) (Some c) (aread i a))) misscred.
Proof.
  destruct (aread i a) as [c |] eqn:E.
  - apply sdec_l. apply (existT _ c). apply cwe_tid_refl.
  - apply sdec_r. apply (MC_ANCH i).
Defined.

Definition qanc_ok (a : acol) (i : nat) : bool :=
  match aread i a with Some _ => true | None => false end.

(* 三分派与 bool 准入的互通不经本体展开桥接，而经凭证型刻画：
   qin_dc/qval_dc/qanc_dc 的 left 支型 == qin_correct/qval_correct/qanc_correct
   中与各自 bool 准入 ⟺ 的凭证型（prod cwe_nle 对 / sigT 券面 / sigT 锚面）——
   两路定义被同一凭证型钉死，一致性由类型而非引理承担。 *)

(* --- 正确性定理：准入 ⟺ 存在凭证（sigT 携带；⟺ 用 iffT） --- *)

Theorem qin_correct : forall (d : dtab) (i j : nat),
  iffT (cwe_tid bool (qin_ok d i j) true)
       (prod (cwe_nle i (dlen d)) (cwe_nle j (dlen d))).
Proof.
  intros d i j. apply (mkIffT _ _).
  - intros H. unfold qin_ok in H.
    tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
    exact (pair (cwe_nle_of_leb (dlen d) i (cwe_tid_eq bool _ true E1))
                (cwe_nle_of_leb (dlen d) j (cwe_tid_eq bool _ true E2))).
  - intros p. destruct p as [Ha Hb].
    pose proof (cwe_nle_leb (dlen d) i Ha) as T1. tidQ T1 E1.
    pose proof (cwe_nle_leb (dlen d) j Hb) as T2. tidQ T2 E2.
    unfold qin_ok.
    apply (cwe_tid_eq bool (Nat.leb i (dlen d) && Nat.leb j (dlen d)) true).
    rewrite E1, E2. reflexivity.
Qed.

Theorem qval_correct : forall (v : option (nat * Z)) (i : nat),
  iffT (cwe_tid bool (qval_ok v i) true)
       (sigT (fun w : Z => cwe_tid (option (nat * Z)) (Some (i, w)) v)).
Proof.
  intros v i. apply (mkIffT _ _).
  - intros H. unfold qval_ok in H. destruct v as [[h w] |] eqn:Ev.
    + simpl in H. destruct (Nat.eqb h i) eqn:Eh.
      * apply (existT _ w).
        apply Nat.eqb_eq in Eh.
        exact (cwe_tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
                 (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
      * tidQ H E. discriminate E.
    + simpl in H. tidQ H E. discriminate E.
  - intros [w H]. unfold qval_ok. destruct v as [[h w0] |] eqn:Ev.
    + tidQ H E. injection E as Ei Ew.
      rewrite Ei. simpl.
      exact (cwe_tid_eq bool (Nat.eqb h h) true (Nat.eqb_refl h)).
    + tidQ H E. discriminate E.
Qed.

Theorem qanc_correct : forall (a : acol) (i : nat),
  iffT (cwe_tid bool (qanc_ok a i) true)
       (sigT (fun c : Z => cwe_tid (option Z) (Some c) (aread i a))).
Proof.
  intros a i. apply (mkIffT _ _).
  - intros H. unfold qanc_ok in H. destruct (aread i a) as [c |] eqn:E.
    + apply (existT _ c). apply cwe_tid_refl.
    + tidQ H E2. discriminate E2.
  - intros [c H]. unfold qanc_ok. destruct (aread i a) as [c0 |] eqn:E.
    + apply cwe_tid_refl.
    + tidQ H E2. discriminate E2.
Qed.

(* ===================================================================== *)
(* 5. 件 2：结构性拒答——账态 clst + 问答机 qask + 总分派 qdc                   *)
(* ===================================================================== *)

(* CL 账态 = 差表 + 单槽头券 + 锚义务已闭列（窗即差表本身，dtab 定长归纳） *)
Record clst : Set := mkCL
  { cld : dtab                    (* 差表（[内]类唯一数据源）            *)
  ; clv : option (nat * Z)        (* 单槽头券：Some (h, w) = 头券未花    *)
  ; cla : acol }.                 (* 锚义务已闭列（[锚]类唯一数据源）     *)

(* 问答机（三元组版）：每类只读自己的凭证通道——
   [内]读差表 dsub；[值]读头券 vs_val；[锚]读锚闭 aread。绝无跨通道偷读。 *)
Definition qaskR (d : dtab) (v : option (nat * Z)) (a : acol) (q : qtype) : qans :=
  match q with
  | QIN i j =>
      if Nat.leb i (dlen d)
      then (if Nat.leb j (dlen d)
            then qans_val (dsub d i j)
            else qans_rej (MC_RANGE j))
      else qans_rej (MC_RANGE i)
  | QVAL i =>
      if qval_ok v i then qans_val (vs_val v) else qans_rej MC_VSLOT
  | QANC i a0 =>
      if qanc_ok a i
      then qans_val (match aread i a with Some c => c - a0 | None => 0 end)
      else qans_rej (MC_ANCH i)
  end.

(* 准入谓词（bool）：与问答机同源分派 *)
Definition qadmitR (d : dtab) (v : option (nat * Z)) (a : acol) (q : qtype) : bool :=
  match q with
  | QIN i j => qin_ok d i j
  | QVAL i => qval_ok v i
  | QANC i _ => qanc_ok a i
  end.

(* 账态版封装：问答机与准入谓词 *)
Definition qask (s : clst) (q : qtype) : qans := qaskR (cld s) (clv s) (cla s) q.
Definition qadmit (s : clst) (q : qtype) : bool := qadmitR (cld s) (clv s) (cla s) q.

(* 准入与答判读逐点一致（宪法内部自洽） *)
Lemma qadmit_isin : forall (s : clst) (q : qtype),
  cwe_tid bool (qadmit s q) (qans_isans (qask s q)).
Proof.
  intros s q. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans, qin_ok.
    destruct (Nat.leb i (dlen (cld s))); destruct (Nat.leb j (dlen (cld s)));
      apply cwe_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qval_ok (clv s) i); apply cwe_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qanc_ok (cla s) i); apply cwe_tid_refl.
Qed.

(* 宪法判定面总分派：left = 答值见证；right = 结构性拒答见证（携型标） *)
Definition qdc (s : clst) (q : qtype)
  : sdec (sigT (fun z : Z => cwe_tid qans (qask s q) (qans_val z)))
         (sigT (fun mc : misscred => cwe_tid qans (qask s q) (qans_rej mc))).
Proof.
  destruct q as [i j | i | i a0].
  - unfold qask, qaskR.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply sdec_l. apply (existT _ (dsub (cld s) i j)). apply cwe_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE j)). apply cwe_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply cwe_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply cwe_tid_refl.
  - unfold qask, qaskR. destruct (qval_ok (clv s) i) eqn:Ev.
    + apply sdec_l. apply (existT _ (vs_val (clv s))). apply cwe_tid_refl.
    + apply sdec_r. apply (existT _ MC_VSLOT). apply cwe_tid_refl.
  - unfold qask, qaskR. destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply sdec_l.
      apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply cwe_tid_refl.
    + apply sdec_r. apply (existT _ (MC_ANCH i)). apply cwe_tid_refl.
Defined.

(* 总分派规范：裁决位 qdc_b 与准入 bool 逐点一致（宪法内部自洽的 bool 面）；
   分支的凭证内容一致性由 qadmit_answer / qadmit_reject 承担 *)
Definition qdc_b (s : clst) (q : qtype) : bool :=
  match qdc s q with sdec_l _ _ _ => true | sdec_r _ _ _ => false end.

Theorem qdc_spec : forall (s : clst) (q : qtype), cwe_tid bool (qdc_b s q) (qadmit s q).
Proof.
  intros s q. unfold qdc_b. destruct (qdc s q) as [Cz | Cm].
  - destruct Cz as [w Hw].
    exact (cwe_tid_sym bool (qadmit s q) true
             (cwe_tid_trans bool (qadmit s q) (qans_isans (qask s q)) true
                (qadmit_isin s q)
                  (cwe_tid_cong qans_isans (qask s q) (qans_val w) Hw))).
  - destruct Cm as [mc Hmc].
    exact (cwe_tid_sym bool (qadmit s q) false
             (cwe_tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
                (qadmit_isin s q)
                  (cwe_tid_cong qans_isans (qask s q) (qans_rej mc) Hmc))).
Qed.

(* 拒答诚实性：凡 qask 输出拒答支，准入必为 false（拒答=显式构造，非失败） *)
Theorem qrej_admit_false : forall (s : clst) (q : qtype) (mc : misscred),
  cwe_tid qans (qask s q) (qans_rej mc) -> cwe_tid bool (qadmit s q) false.
Proof.
  intros s q mc H.
  exact (cwe_tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
           (qadmit_isin s q) (cwe_tid_cong qans_isans (qask s q) (qans_rej mc) H)).
Qed.

(* 准入真 ⟹ 答值支显式构造（携答值见证） *)
Theorem qadmit_answer : forall (s : clst) (q : qtype), cwe_tid bool (qadmit s q) true ->
  sigT (fun z : Z => cwe_tid qans (qask s q) (qans_val z)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply (existT _ (dsub (cld s) i j)). apply cwe_tid_refl.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + apply (existT _ (vs_val (clv s))). apply cwe_tid_refl.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply cwe_tid_refl.
    + tidQ H E. discriminate E.
Qed.

(* 准入假 ⟹ 拒答支显式构造（携缺失凭证型标见证）——结构性拒答的存在性 *)
Theorem qadmit_reject : forall (s : clst) (q : qtype), cwe_tid bool (qadmit s q) false ->
  sigT (fun mc : misscred => cwe_tid qans (qask s q) (qans_rej mc)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_RANGE j)). apply cwe_tid_refl.
    + apply (existT _ (MC_RANGE i)). apply cwe_tid_refl.
    + apply (existT _ (MC_RANGE i)). apply cwe_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ MC_VSLOT). apply cwe_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_ANCH i)). apply cwe_tid_refl.
Qed.

(* --- 头券生命周期：[值]类答一次即焚，焚后再问 = 结构性拒答附缺头券型标 --- *)

Definition clburn (s : clst) (i : nat) : clst := mkCL (cld s) None (cla s).

Theorem val_fresh_answer : forall (d : dtab) (a : acol) (i : nat) (w : Z),
  cwe_tid qans (qask (mkCL d (Some (i, w)) a) (QVAL i)) (qans_val w).
Proof.
  intros d a i w. unfold qask, qaskR, qval_ok. simpl.
  rewrite Nat.eqb_refl. apply cwe_tid_refl.
Qed.

Theorem val_burn_reject : forall (s : clst) (i : nat),
  cwe_tid qans (qask (clburn s i) (QVAL i)) (qans_rej MC_VSLOT).
Proof.
  intros s i. unfold qask, qaskR, clburn, qval_ok. simpl. apply cwe_tid_refl.
Qed.

(* ===================================================================== *)
(* 6. 件 3：[内]类平移不变性（分型押注的语法化）                               *)
(* ===================================================================== *)

(* CL 2.0 押注的分型形式：[内]类裁决在差表 gauge 平移下逐字不变。
   对照 pot_shift_moves：绝对读出恰移动 c——故绝对问题在 [内]类语法内
   不可问出（问了也必得到平移不变的答案，即被类型系统挡在差表语言外）。 *)
Theorem qin_gauge_invariant : forall (d : dtab) (c : Z) (v : option (nat * Z))
                                     (a : acol) (i j : nat),
  cwe_tid qans (qask (mkCL (dshift d c) v a) (QIN i j))
           (qask (mkCL d v a) (QIN i j)).
Proof.
  intros d c v a i j. unfold qask, qaskR. cbn [cld clv cla].
  pose proof (dlen_shift d c) as DL. tidQ DL Edl. rewrite Edl.
  destruct (Nat.leb i (dlen d)) eqn:Ei; destruct (Nat.leb j (dlen d)) eqn:Ej.
  - apply tid_qans_val. apply dsub_shift_invariant.
    + exact (cwe_nle_of_leb (dlen d) i (cwe_tid_eq bool (Nat.leb i (dlen d)) true Ei)).
    + exact (cwe_nle_of_leb (dlen d) j (cwe_tid_eq bool (Nat.leb j (dlen d)) true Ej)).
  - apply cwe_tid_refl.
  - apply cwe_tid_refl.
  - apply cwe_tid_refl.
Qed.

End CLQueryBody.

End UpCLQueryISO.

(* ---------- UpBudgetReal ---------- *)
Module BudgetReal.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
(* ============================================================ *)
(* UpBudgetReal.v —— 几何击穿的 Real 层显式迭代预算定理            *)
(*                                                              *)
(* 论文 4（梯度动力学收敛）主贡献「显式迭代预算」的 Real 层载体：    *)
(* 根文件 ConvergenceCauchy 节的接口前提                          *)
(*   r_arch_pow : 0 < a -> 0 < eps -> sigT (fun n => a·κ^n < eps) *)
(* 至今只有接口假设形态；本文件在具体柯西实数（CW214KL_scan 的     *)
(* Real := sigT (fun u : Qseq => cauchy u)）上闭合该缺口：        *)
(*                                                              *)
(* 主交付 r_arch_pow_real：                                      *)
(*   ∀κ a eps（0<κ<1、0<a、0<eps），存在显式 nat 见证 N 使          *)
(*   a·κ^N < eps。                                               *)
(* 构造路线（路线 A，纯 Real 层，无需 Q 层绕行）：                  *)
(*   令 i := 1/κ > 1，c := i − 1 > 0。Bernoulli 不等式             *)
(*   i^N ≥ 1 + (N#1)·c 给出幂下界；预算实数 y := (a/eps)/c 经      *)
(*   real_arch（Real 层 Archimedean，217 根内已证）解出 N，        *)
(*   再经倒数反变（real_inv_pos_lt_contra）与 pow·inv 恒等式        *)
(*   回接 a·κ^N < eps。N 的显式形态：real_arch 给出的 nat。        *)
(*                                                              *)
(* 件 1：预算条件充分性（log 闭式条件）                            *)
(*   r_pow_log_form      log(κ^N) == (N#1)·log κ（归纳）           *)
(*   log_kappa_neg       0<κ<1 ⟹ −log κ > 0（hlogz_strict 放电）   *)
(*   budget_cond_sufficient  N·|log κ| > log a − log eps ⟹ a·κ^N<eps *)
(*   （经 cauchy_real_exp_mono 严格单调 + cw_log_exp_right 反演回接）*)
(*                                                              *)
(* 件 3：论文 4 定理 4.10 尾界形态（纯序代数）                      *)
(*   real_pow_anti_mono  p ≤ q ⟹ κ^q ≤ κ^p                        *)
(*   geo_tail_budget     N ≤ min m n ∧ a·κ^N < eps ⟹ a·κ^{min} < eps *)
(*   budget_min_tail     预算 N 的存在性 + min 尾界组合              *)
(*                                                              *)
(* 纪律：纯构造性（禁词零出现，见交付报告 G1）；                    *)
(*       Set 层语句（real_lt/real_le/real_eq/sigT/And）；           *)
(*       全部 Qed 闭合；消费根内已证机器不重证。                    *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============ 0. 具体实数层幂（Real 层 r_pow） ============ *)

Fixpoint real_pow (x : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_mult x (real_pow x m)
  end.

(* 与任务书同名接口：r_pow kappa N 即 real_pow kappa N *)
Notation r_pow := real_pow (only parsing).

(* 幂对 real_eq 的相容性 *)
Lemma real_pow_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (real_pow x n) (real_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [real_pow].
    apply (RealSetoid.real_eq_mult_compat x (real_pow x m) y (real_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* 幂正性：0 < x ⟹ 0 < x^n *)
Lemma cwe_real_pow_pos : forall (x : Real) (n : nat),
  real_lt real_zero x -> real_lt real_zero (real_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [real_pow]. exact (real_mult_pos_compat x (real_pow x m) Hx IH).
Qed.

(* ============ 1. 基本代数小工具（217 根内缺位的补齐） ============ *)

(* 0#1 == 0（nat 嵌入零点） *)
Lemma real_const_zero_thm : real_eq (real_const (Z.of_nat 0 # 1)) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  change (projT1 (real_const (Z.of_nat 0 # 1)) n) with 0%Q.
  change (projT1 real_zero n) with 0%Q.
  ring.
Qed.

(* 1·x == x（根内 real_mult_one 是 x·1 形态） *)
Lemma real_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one)).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* 0·x == 0（根内 real_mult_zero 是 x·0 形态） *)
Lemma real_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_zero)).
  - apply real_mult_comm.
  - apply real_mult_zero.
Qed.

(* nat 嵌入乘法后继：(S n)#1·x == (n#1)·x + x *)
Lemma real_nat_mult_succ : forall (n : nat) (x : Real),
  real_eq (real_mult (real_const (Z.of_nat (Datatypes.S n) # 1)) x)
          (real_plus (real_mult (real_const (Z.of_nat n # 1)) x) x).
Proof.
  intros n x.
  apply (real_eq_trans _ (real_mult (real_plus (real_const (Z.of_nat n # 1)) real_one) x)).
  - apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat (Datatypes.S n) # 1)) x
                                          (real_plus (real_const (Z.of_nat n # 1)) real_one) x).
    + apply b4_lift_succ.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat n # 1)) x)
                                      (real_mult real_one x))).
    + apply (real_eq_sym _ _ (real_distrib_r_local (real_const (Z.of_nat n # 1)) real_one x)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (real_const (Z.of_nat n # 1)) x)
                                            (real_mult real_one x)
                                            (real_mult (real_const (Z.of_nat n # 1)) x) x).
      * apply real_eq_refl.
      * apply real_mult_one_l.
Qed.

(* 倒数唯一性补充：inv 1 == 1（根内 real_inv_one_local 已有，直接消费） *)
(* （此处不重证；见 real_inv_one_local） *)

(* 倒数正性专用：1 < 1/κ 的桥（real_inv_pos_lt_contra + inv 1 == 1） *)

(* ============ 2. 幂·倒数恒等式（κ^N · (1/κ)^N == 1） ============ *)

Lemma real_pow_inv_pair : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_mult (real_pow k n) (real_pow (real_inv_pos k Hk) n)) real_one.
Proof.
  intros k Hk n. induction n as [| m IH].
  - cbn [real_pow]. apply real_mult_one.
  - cbn [real_pow].
    (* (k·k^m)·(i·i^m) == 1，i := 1/κ *)
    apply (real_eq_trans _ (real_mult (real_mult (real_pow k m) k)
                                      (real_mult (real_inv_pos k Hk)
                                                 (real_pow (real_inv_pos k Hk) m)))).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult k (real_pow k m))
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))
               (real_mult (real_pow k m) k)
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult (real_pow k m)
                                        (real_mult k (real_mult (real_inv_pos k Hk)
                                                                (real_pow (real_inv_pos k Hk) m))))).
      * apply (real_eq_sym _ _ (real_mult_assoc (real_pow k m) k
                         (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))).
      * apply (real_eq_trans _ (real_mult (real_pow k m)
                                          (real_mult (real_mult k (real_inv_pos k Hk))
                                                     (real_pow (real_inv_pos k Hk) m)))).
        -- apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                   (real_mult k (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))
                   (real_pow k m)
                   (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))).
           ++ apply real_eq_refl.
           ++ apply (real_mult_assoc k (real_inv_pos k Hk)
                                        (real_pow (real_inv_pos k Hk) m)).
        -- apply (real_eq_trans _ (real_mult (real_pow k m)
                                             (real_mult real_one (real_pow (real_inv_pos k Hk) m)))).
           ++ apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                      (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))
                      (real_pow k m)
                      (real_mult real_one (real_pow (real_inv_pos k Hk) m))).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_mult_compat (real_mult k (real_inv_pos k Hk))
                          (real_pow (real_inv_pos k Hk) m) real_one (real_pow (real_inv_pos k Hk) m)).
                 --- exact (real_inv_pos_correct k Hk).
                 --- apply real_eq_refl.
           ++ apply (real_eq_trans _ (real_mult (real_pow k m)
                                                (real_pow (real_inv_pos k Hk) m))).
              ** apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                          (real_mult real_one (real_pow (real_inv_pos k Hk) m))
                          (real_pow k m) (real_pow (real_inv_pos k Hk) m)).
                 --- apply real_eq_refl.
                 --- apply real_mult_one_l.
              ** exact IH.
Qed.

(* ============ 3. le/lt 辅助（1 ≤ 1+x、0 ≤ (n#1)·x、y < 1+y） ============ *)

Lemma cwe_real_le_one_plus : forall x : Real,
  real_le real_zero x -> real_le real_one (real_plus real_one x).
Proof.
  intros x Hx.
  apply (real_le_trans _ (real_plus real_one real_zero)).
  - apply real_eq_le_bridge.
    apply (real_eq_sym _ _ (real_plus_zero real_one)).
  - exact (real_le_plus_compat real_one real_one real_zero x (real_le_refl real_one) Hx).
Qed.

Lemma real_lt_plus_one : forall y : Real, real_lt y (real_plus real_one y).
Proof.
  intro y.
  apply (real_eq_lt_lt y (real_plus real_zero y) (real_plus real_one y)).
  - exact (real_eq_sym (real_plus real_zero y) y (sf_real_plus_zero_l y)).
  - exact (real_lt_plus_compat_lt_le real_zero real_one y y real_lt_zero_one (real_le_refl y)).
Qed.

(* (n#1)·x 非负：0 < x ⟹ 0 ≤ (n#1)·x（nat 嵌入倍数非负） *)
Lemma real_nat_mult_nonneg : forall (n : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (real_mult (real_const (Z.of_nat n # 1)) x).
Proof.
  intros n x Hx. induction n as [| m IH].
  - apply real_eq_le_bridge.
    apply (real_eq_trans _ (real_mult real_zero x)).
    + apply (real_eq_sym _ _ (real_mult_zero_l x)).
    + apply (RealSetoid.real_eq_mult_compat real_zero x (real_const (Z.of_nat 0 # 1)) x).
      * apply (real_eq_sym _ _ real_const_zero_thm).
      * apply real_eq_refl.
  - apply real_lt_le_bridge.
    apply (real_lt_eq_lt _ (real_plus (real_mult (real_const (Z.of_nat m # 1)) x) x)).
    + apply (real_lt_eq_lt _ (real_plus x (real_mult (real_const (Z.of_nat m # 1)) x))).
      * apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)).
        -- exact (real_eq_sym _ _ (real_plus_zero real_zero)).
        -- exact (real_lt_plus_compat_lt_le real_zero x real_zero
                    (real_mult (real_const (Z.of_nat m # 1)) x) Hx IH).
      * apply real_plus_comm.
    + apply (real_eq_sym _ _ (real_nat_mult_succ m x)).
Qed.

(* ============ 4. Bernoulli 幂下界：(1+c)^n ≥ 1 + (n#1)·c（c > 0） ============ *)

Lemma bernoulli_pow : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_le (real_plus real_one (real_mult (real_const (Z.of_nat n # 1)) c))
          (real_pow (real_plus real_one c) n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - cbn [real_pow].
    apply (real_le_trans _ real_one).
    + apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one real_zero)).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat 0 # 1)) c) real_one real_zero).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _ (real_mult real_zero c)).
           ++ apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat 0 # 1)) c
                       real_zero c).
              ** exact real_const_zero_thm.
              ** apply real_eq_refl.
           ++ apply (real_mult_zero_l c).
      * exact (real_plus_zero real_one).
    + apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_plus (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c)) c)).
    + (* 1 + (S m)#1·c == (1 + m#1·c) + c *)
      apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c))).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat (Datatypes.S m) # 1)) c)
                 real_one
                 (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c)).
        -- apply real_eq_refl.
        -- apply (real_nat_mult_succ m c).
      * apply real_plus_assoc.
    + (* (1 + m#1·c) + c ≤ (1+c)·(1+c)^m *)
      apply (real_le_trans _ (real_plus (real_pow (real_plus real_one c) m)
                                        (real_mult c (real_pow (real_plus real_one c) m)))).
      * assert (Hx0 : real_le real_zero (real_mult (real_const (Z.of_nat m # 1)) c))
          by exact (real_nat_mult_nonneg m c Hc).
        assert (H1P : real_le real_one (real_pow (real_plus real_one c) m)).
        { apply (real_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c))).
          - exact (cwe_real_le_one_plus _ Hx0).
          - exact IH. }
        apply (real_le_plus_compat _ _ _ _ IH).
        (* c ≤ c·(1+c)^m *)
        apply (real_le_trans _ (real_mult c real_one)).
        -- apply real_eq_le_bridge.
           apply (real_eq_sym _ _ (real_mult_one c)).
        -- apply (real_le_trans _ (real_mult real_one c)).
           ++ apply real_eq_le_bridge.
              exact (real_mult_comm c real_one).
           ++ apply (real_le_trans _ (real_mult (real_pow (real_plus real_one c) m) c)).
              ** exact (real_le_mult_compat real_one (real_pow (real_plus real_one c) m) c Hc H1P).
              ** apply real_eq_le_bridge.
                 exact (real_mult_comm (real_pow (real_plus real_one c) m) c).
      * (* P + c·P == (1+c)·P *)
        apply real_eq_le_bridge.
        apply (real_eq_trans _ (real_plus (real_mult real_one (real_pow (real_plus real_one c) m))
                                          (real_mult c (real_pow (real_plus real_one c) m)))).
        -- apply (RealSetoid.real_eq_plus_compat (real_pow (real_plus real_one c) m)
                    (real_mult c (real_pow (real_plus real_one c) m))
                    (real_mult real_one (real_pow (real_plus real_one c) m))
                    (real_mult c (real_pow (real_plus real_one c) m))).
           ++ apply (real_eq_sym _ _ (real_mult_one_l (real_pow (real_plus real_one c) m))).
           ++ apply real_eq_refl.
        -- exact (real_distrib_r_local real_one c (real_pow (real_plus real_one c) m)).
Qed.


(* ============ 5. 件 2 主定理：几何击穿的 Real 层显式 nat 预算 ============ *)
(*   N 的显式形态：real_arch 在预算实数 y := (a/eps)/(1/κ − 1) 上解出的 nat。 *)

Theorem r_arch_pow_real :
  forall (kappa : Real) (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (a : Real) (Ha : real_lt real_zero a) (eps : Real) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps).
Proof.
  intros kappa Hk1 Hk2 a Ha eps Heps.
  assert (Hinvpos : real_lt real_zero (real_inv_pos kappa Hk1))
    by exact (real_inv_pos_pos kappa Hk1).
  assert (HoneLtInv : real_lt real_one (real_inv_pos kappa Hk1)).
  { apply (real_eq_lt_lt real_one (real_inv_pos real_one real_lt_zero_one)
                         (real_inv_pos kappa Hk1)).
    - apply (real_eq_sym _ _ real_inv_one_local).
    - exact (real_inv_pos_lt_contra kappa real_one Hk1 real_lt_zero_one Hk2). }
  assert (Hc : real_lt real_zero (real_plus (real_inv_pos kappa Hk1) (real_opp real_one)))
    by exact (real_lt_opp_plus real_one (real_inv_pos kappa Hk1) HoneLtInv).
  assert (Hax : real_lt real_zero (real_mult a (real_inv_pos eps Heps)))
    by exact (real_mult_pos_compat a (real_inv_pos eps Heps) Ha (real_inv_pos_pos eps Heps)).
  set (c := real_plus (real_inv_pos kappa Hk1) (real_opp real_one)) in Hc |- *.
  set (x := real_mult a (real_inv_pos eps Heps)) in Hax |- *.
  assert (Hyc : real_lt real_zero (real_mult x (real_inv_pos c Hc)))
    by exact (real_mult_pos_compat x (real_inv_pos c Hc) Hax (real_inv_pos_pos c Hc)).
  destruct (real_arch (real_mult x (real_inv_pos c Hc))) as [N [HN2 HN]].
  (* x < (N#1)·c：(x·(1/c))·c == x（real_mult_div 的换形），再乘 c 保序 *)
  assert (Hxc_lt : real_lt x (real_mult (real_const (Z.of_nat N # 1)) c)).
  { apply (real_eq_lt_lt x (real_mult (real_mult x (real_inv_pos c Hc)) c)).
    - apply (real_eq_trans _ (real_mult c (real_mult x (real_inv_pos c Hc)))).
      + apply (real_eq_sym _ _ (real_mult_div c x Hc)).
      + apply real_mult_comm.
    - exact (real_mult_lt_compat (real_mult x (real_inv_pos c Hc))
               (real_const (Z.of_nat N # 1)) c HN Hc). }
  (* 1 + c == 1/κ *)
  assert (Honec : real_eq (real_plus real_one c) (real_inv_pos kappa Hk1)).
  { unfold c. apply (real_eq_trans _ (real_plus (real_plus real_one (real_inv_pos kappa Hk1))
                                                (real_opp real_one))).
    - apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_plus (real_inv_pos kappa Hk1) real_one)
                                        (real_opp real_one))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus real_one (real_inv_pos kappa Hk1)) (real_opp real_one)
                 (real_plus (real_inv_pos kappa Hk1) real_one) (real_opp real_one)).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1)
                                          (real_plus real_one (real_opp real_one)))).
        * apply (real_eq_sym _ _ (real_plus_assoc (real_inv_pos kappa Hk1) real_one
                                                    (real_opp real_one))).
        * apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1) real_zero)).
          -- apply (RealSetoid.real_eq_plus_compat (real_inv_pos kappa Hk1)
                      (real_plus real_one (real_opp real_one))
                      (real_inv_pos kappa Hk1) real_zero).
             ++ apply real_eq_refl.
             ++ apply real_plus_opp.
          -- apply (real_plus_zero (real_inv_pos kappa Hk1)). }
  (* x < 1 + (N#1)·c ≤ (1+c)^N == (1/κ)^N（Bernoulli le + 前段 strict） *)
  assert (Hkey : real_lt x (real_pow (real_inv_pos kappa Hk1) N)).
  { apply (real_lt_eq_lt _ (real_pow (real_plus real_one c) N)).
    - apply (real_lt_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat N # 1)) c))).
      + apply (real_lt_trans _ (real_mult (real_const (Z.of_nat N # 1)) c)).
        * exact Hxc_lt.
        * exact (real_lt_plus_one _).
      + exact (bernoulli_pow c Hc N).
    - apply (real_pow_eq_compat _ _ N Honec). }
  (* κ^N == 1/(1/κ)^N（pow·inv 恒等式 + 倒数唯一） *)
  assert (HposN : real_lt real_zero (real_pow (real_inv_pos kappa Hk1) N))
    by exact (cwe_real_pow_pos _ N Hinvpos).
  assert (Hpowinv : real_eq (real_pow kappa N)
                            (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
  { apply (real_inv_unique (real_pow (real_inv_pos kappa Hk1) N) (real_pow kappa N)
                           (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - apply (real_eq_trans _ (real_mult (real_pow kappa N)
                                        (real_pow (real_inv_pos kappa Hk1) N))).
      + apply real_mult_comm.
      + exact (real_pow_inv_pair kappa Hk1 N).
    - exact (real_inv_pos_correct (real_pow (real_inv_pos kappa Hk1) N) HposN). }
  (* 1/x == eps·(1/a)（real_inv_unique 于 x·(eps·(1/a)) == 1） *)
  assert (Hinva : real_eq (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_inv_unique x (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
    - exact (real_inv_pos_correct x Hax).
    - apply (real_eq_trans _ (real_mult a
                 (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha))))).
      + apply (real_eq_sym _ _ (real_mult_assoc a (real_inv_pos eps Heps)
                                  (real_mult eps (real_inv_pos a Ha)))).
      + apply (real_eq_trans _ (real_mult a
                 (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)))).
        * apply (RealSetoid.real_eq_mult_compat a
                    (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha)))
                    a
                    (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))).
          -- apply real_eq_refl.
          -- apply (real_mult_assoc (real_inv_pos eps Heps) eps
                                                       (real_inv_pos a Ha)).
        * apply (real_eq_trans _ (real_mult a (real_mult real_one (real_inv_pos a Ha)))).
          -- apply (RealSetoid.real_eq_mult_compat a
                      (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))
                      a
                      (real_mult real_one (real_inv_pos a Ha))).
             ++ apply real_eq_refl.
             ++ apply (RealSetoid.real_eq_mult_compat
                          (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)
                          real_one (real_inv_pos a Ha)).
                ** apply (real_eq_trans _ (real_mult eps (real_inv_pos eps Heps))).
                   --- apply real_mult_comm.
                   --- exact (real_inv_pos_correct eps Heps).
                ** apply real_eq_refl.
          -- apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha))).
             ++ apply (RealSetoid.real_eq_mult_compat a
                         (real_mult real_one (real_inv_pos a Ha)) a (real_inv_pos a Ha)).
                ** apply real_eq_refl.
                ** apply real_mult_one_l.
             ++ exact (real_inv_pos_correct a Ha). }
  assert (Hinvlt : real_lt (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)
                           (real_inv_pos x Hax)).
  { exact (real_inv_pos_lt_contra x (real_pow (real_inv_pos kappa Hk1) N) Hax HposN Hkey). }
  (* κ^N < eps·(1/a) *)
  assert (Hklt : real_lt (real_pow kappa N) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_eq_lt_lt _ (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - exact Hpowinv.
    - exact (real_lt_eq_lt _ _ _ Hinvlt Hinva). }
  exists N.
  apply (real_lt_eq_lt (real_mult a (real_pow kappa N))
                       (real_mult a (real_mult eps (real_inv_pos a Ha)))).
  - exact (real_mult_lt_compat_l (real_pow kappa N)
             (real_mult eps (real_inv_pos a Ha)) a Hklt Ha).
  - exact (real_mult_div a eps Ha).
Qed.

(* ============ 6. 件 1：log 形态闭式条件（Real 层） ============ *)

(* −log κ > 0：0 < κ < 1 ⟹ log κ < 0（UpHlogZ.hlogz_strict 放电）⟹ opp 反变 *)
Lemma log_kappa_neg : forall (kappa : Real)
                         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one),
  real_lt real_zero (real_opp (real_log kappa Hk1)).
Proof.
  intros kappa Hk1 Hk2.
  assert (Hneg : real_lt (real_log kappa Hk1) real_zero)
    by exact (hlogz_strict kappa Hk1 Hk2).
  apply (real_eq_lt_lt real_zero (real_opp real_zero) (real_opp (real_log kappa Hk1))).
  - apply (real_eq_sym _ _ real_opp_zero).
  - exact (real_opp_lt_compat (real_log kappa Hk1) real_zero Hneg).
Qed.

(* log 幂恒等式：log(κ^N) == (N#1)·log κ（real_log_mult 归纳） *)
Lemma real_pow_log_form : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_log (real_pow k n) (cwe_real_pow_pos k n Hk))
          (real_mult (real_const (Z.of_nat n # 1)) (real_log k Hk)).
Proof.
  intros k Hk n. induction n as [| m IH].
  - apply (real_eq_trans _ real_zero).
    + apply real_log_one.
    + exact (real_eq_sym (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk)) real_zero
               (real_eq_trans (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk))
                              (real_mult real_zero (real_log k Hk)) real_zero
                              (RealSetoid.real_eq_mult_compat
                                 (real_const (Z.of_nat 0 # 1)) (real_log k Hk)
                                 real_zero (real_log k Hk)
                                 real_const_zero_thm (real_eq_refl (real_log k Hk)))
                              (real_mult_zero_l (real_log k Hk)))).
  - cbn [real_pow].
    apply (real_eq_trans _ (real_plus (real_log k Hk)
                                      (real_log (real_pow k m) (cwe_real_pow_pos k m Hk)))).
    + exact (log_inv_mult_thm k (real_pow k m) Hk (cwe_real_pow_pos k m Hk)
               (cwe_real_pow_pos k (Datatypes.S m) Hk)).
    + apply (real_eq_trans _ (real_plus (real_log k Hk)
                   (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk)))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) IH).
      * apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                            (real_log k Hk))).
        -- apply (real_plus_comm (real_log k Hk)
                    (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))).
        -- apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                             (real_log k Hk))).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)).
              ** apply real_eq_refl.
              ** apply real_eq_refl.
           ++ apply (real_eq_sym _ _ (real_nat_mult_succ m (real_log k Hk))).
Qed.

(* 件 1 主件：预算条件充分性
   N·|log κ| > log a − log eps ⟹ a·κ^N < eps
   （经 log 多项式恒等 + cauchy_real_exp_mono 严格单调 + cw_log_exp_right 反演） *)
Theorem budget_cond_sufficient :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (N : nat),
  real_lt (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
          (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1))) ->
  real_lt (real_mult a (real_pow kappa N)) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps N Hcond.

  (* log(a·κ^N) == log a + N#1·logκ *)
  assert (Hlogpow : real_eq (real_log (real_mult a (real_pow kappa N))
                                      (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))
                            (real_plus (real_log a Ha)
                                       (real_mult (real_const (Z.of_nat N # 1))
                                                  (real_log kappa Hk1)))).
  { apply (real_eq_trans _ (real_plus (real_log a Ha)
                                      (real_log (real_pow kappa N) (cwe_real_pow_pos kappa N Hk1)))).
    - exact (real_log_mult a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
               (real_pow_log_form kappa Hk1 N)). }
  (* N#1·logκ == −(N#1·(−logκ)) *)
  assert (Hnegm : real_eq (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1))
                          (real_opp (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1))))).
  { apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1))
                                      (real_opp (real_opp (real_log kappa Hk1))))).
    - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
               (real_eq_sym _ _ (real_opp_opp (real_log kappa Hk1)))).
    - apply real_mult_opp_l. }
  (* 条件换形：log a < N#1·(−logκ) + log eps
     （Hcond 两侧加 log eps：La + −Le < W ⟹ (La + −Le) + Le < W + Le） *)
  assert (Hmid : real_lt (real_log a Ha)
                         (real_plus (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1)))
                                    (real_log eps Heps))).
  { apply (real_eq_lt_lt (real_log a Ha)
            (real_plus (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
                       (real_log eps Heps))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps)))).
      + apply (real_eq_sym _ _).
        apply (real_eq_trans _ (real_plus (real_log a Ha) real_zero)).
        * apply (RealSetoid.real_eq_plus_compat (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps))
                   (real_log a Ha) real_zero).
          -- apply real_eq_refl.
          -- exact (real_eq_trans _ _ _
                     (real_plus_comm (real_opp (real_log eps Heps)) (real_log eps Heps))
                     (real_plus_opp (real_log eps Heps))).
        * apply (real_plus_zero (real_log a Ha)).
      + apply (real_plus_assoc (real_log a Ha) (real_opp (real_log eps Heps))
                                 (real_log eps Heps)).
    - exact (real_lt_plus_compat_lt_le _ _ _ _ Hcond (real_le_refl (real_log eps Heps))). }
  (* 加法消去：x == La − W、La < W + Le ⟹ x < Le（件 1 专用纯加法引理） *)
  assert (Hshift : forall (x La Le W : Real),
            real_eq x (real_plus La (real_opp W)) ->
            real_lt La (real_plus W Le) ->
            real_lt x Le).
  { intros x0 La0 Le0 W0 H1 H2.
    apply (real_eq_lt_lt x0 (real_plus La0 (real_opp W0))).
    - exact H1.
    - apply (real_lt_eq_lt _ (real_plus (real_plus W0 Le0) (real_opp W0))).
      + exact (real_lt_plus_compat_lt_le _ _ _ _ H2 (real_le_refl _)).
      + exact (real_eq_trans
                 (real_plus (real_plus W0 Le0) (real_opp W0))
                 (real_plus W0 (real_plus Le0 (real_opp W0)))
                 Le0
                 (real_eq_sym _ _ (real_plus_assoc W0 Le0 (real_opp W0)))
                 (real_eq_trans
                    (real_plus W0 (real_plus Le0 (real_opp W0)))
                    (real_plus (real_plus W0 (real_opp W0)) Le0)
                    Le0
                    (real_eq_trans
                       (real_plus W0 (real_plus Le0 (real_opp W0)))
                       (real_plus W0 (real_plus (real_opp W0) Le0))
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (RealSetoid.real_eq_plus_compat W0 (real_plus Le0 (real_opp W0)) W0
                          (real_plus (real_opp W0) Le0)
                          (real_eq_refl W0)
                          (real_plus_comm Le0 (real_opp W0)))
                       (real_plus_assoc W0 (real_opp W0) Le0))
                    (real_eq_trans
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (real_plus real_zero Le0)
                       Le0
                       (RealSetoid.real_eq_plus_compat (real_plus W0 (real_opp W0)) Le0
                          real_zero Le0
                          (real_plus_opp W0)
                          (real_eq_refl Le0))
                       (sf_real_plus_zero_l Le0)))). }
  (* 组装：log(a·κ^N) == La + −(N#1·(−logκ))、La < W + Le ⟹ log(a·κ^N) < Le *)
  assert (Hlt : real_lt (real_log (real_mult a (real_pow kappa N))
                                  (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))
                        (real_log eps Heps)).
  { apply (Hshift _ (real_log a Ha) (real_log eps Heps)
             (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1)))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1)))).
      + exact Hlogpow.
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) Hnegm).
    - exact Hmid. }
  (* exp 严格单调 + e^{log y} == y 反演闭合 *)
  apply (real_eq_lt_lt (real_mult a (real_pow kappa N))
           (cauchy_real_exp (real_log (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1))))
           eps).
  - apply (real_eq_sym _ _ (cw_log_exp_right (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))).
  - apply (real_lt_eq_lt _ (cauchy_real_exp (real_log eps Heps))).
    + exact (cauchy_real_exp_mono _ _ Hlt).
    + exact (cw_log_exp_right eps Heps).
Qed.

(* ============ 7. 件 3：论文 4 定理 4.10 尾界形态（纯序代数） ============ *)

(* 幂加法：κ^(p+j) == κ^p · κ^j *)
Lemma real_pow_add_thm : forall (k : Real) (p j : nat),
  real_eq (real_pow k (p + j)%nat) (real_mult (real_pow k p) (real_pow k j)).
Proof.
  intros k p j. induction p as [| p IH].
  - change (real_pow k (0 + j)%nat) with (real_pow k j).
    change (real_pow k 0) with real_one.
    apply (real_eq_sym _ _ (real_mult_one_l (real_pow k j))).
  - replace (Datatypes.S p + j)%nat with (Datatypes.S (p + j))%nat by lia.
    change (real_pow k (Datatypes.S (p + j))) with
           (real_mult k (real_pow k (p + j))).
    apply (real_eq_trans _ (real_mult k (real_mult (real_pow k p) (real_pow k j)))).
    + apply (RealSetoid.real_eq_mult_compat k (real_pow k (p + j)%nat) k
               (real_mult (real_pow k p) (real_pow k j))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _ (real_mult (real_mult k (real_pow k p)) (real_pow k j))).
      * exact (real_mult_assoc k (real_pow k p) (real_pow k j)).
      * apply real_eq_refl.
Qed.

(* κ ≤ 1 ⟹ κ^j ≤ 1 *)
Lemma real_pow_le_one : forall (k : Real) (Hk1 : real_lt real_zero k)
                          (Hk2 : real_le k real_one) (j : nat),
  real_le (real_pow k j) real_one.
Proof.
  intros k Hk1 Hk2 j. induction j as [| j IH].
  - apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_mult k real_one)).
    + apply (real_le_trans _ (real_mult (real_pow k j) k)).
      * apply real_eq_le_bridge. exact (real_mult_comm k (real_pow k j)).
      * apply (real_le_trans _ (real_mult real_one k)).
        -- exact (real_le_mult_compat (real_pow k j) real_one k Hk1 IH).
        -- apply real_eq_le_bridge.
           apply (real_eq_trans _ k).
           ++ exact (real_mult_one_l k).
           ++ apply (real_eq_sym _ _ (real_mult_one k)).
      + apply (real_le_trans _ k).
        * apply real_eq_le_bridge. exact (real_mult_one k).
        * exact Hk2.
Qed.

(* 幂反单调：0 < κ ≤ 1、p ≤ q ⟹ κ^q ≤ κ^p *)
Lemma real_pow_anti_mono : forall (k : Real) (Hk1 : real_lt real_zero k)
                              (Hk2 : real_le k real_one) (p q : nat),
  (p <= q)%nat -> real_le (real_pow k q) (real_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hle.
  assert (Hcore : forall j : nat,
            real_le (real_pow k (p + j)%nat) (real_pow k p)).
  { intros j.
    assert (Heq : real_eq (real_pow k (p + j)%nat)
                          (real_mult (real_pow k p) (real_pow k j)))
      by exact (real_pow_add_thm k p j).
    apply (real_le_trans _ (real_mult (real_pow k p) (real_pow k j))).
    - apply real_eq_le_bridge. exact Heq.
    - apply (real_le_trans _ (real_mult (real_pow k j) (real_pow k p))).
      + apply real_eq_le_bridge. exact (real_mult_comm (real_pow k p) (real_pow k j)).
      + apply (real_le_trans _ (real_mult real_one (real_pow k p))).
        * exact (real_le_mult_compat (real_pow k j) real_one (real_pow k p)
                   (cwe_real_pow_pos k p Hk1) (real_pow_le_one k Hk1 Hk2 j)).
        * apply real_eq_le_bridge. exact (real_mult_one_l (real_pow k p)). }
  assert (Hq : q = (p + (q - p))%nat) by lia.
  rewrite Hq. apply Hcore.
Qed.

(* 预算下降：N ≤ min m n 且 a·κ^N < eps ⟹ a·κ^{min m n} < eps
   （论文 4 定理 4.10 尾界 a·κ^{min m n} 的预算放电，纯序代数） *)
Theorem geo_tail_budget :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (m n N : nat),
  (N <= Nat.min m n)%nat ->
  real_lt (real_mult a (real_pow kappa N)) eps ->
  real_lt (real_mult a (real_pow kappa (Nat.min m n))) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps m n N Hmin Hbudget.
  assert (Hk2le : real_le kappa real_one)
    by exact (real_lt_le_bridge kappa real_one Hk2).
  apply (real_le_lt_trans _ (real_mult a (real_pow kappa N))).
  - apply (real_le_trans _ (real_mult (real_pow kappa (Nat.min m n)) a)).
    + apply real_eq_le_bridge.
      exact (real_mult_comm a (real_pow kappa (Nat.min m n))).
    + apply (real_le_trans _ (real_mult (real_pow kappa N) a)).
      * exact (real_le_mult_compat (real_pow kappa (Nat.min m n))
                  (real_pow kappa N) a Ha
                  (real_pow_anti_mono kappa Hk1 Hk2le N (Nat.min m n) Hmin)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm (real_pow kappa N) a).
  - exact Hbudget.
Qed.

(* 组合形态：给出显式预算 N，min 尾界随之放电（定理 4.10 Real 层组装） *)
Theorem budget_min_tail :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => forall (p q : nat),
    (N <= Nat.min p q)%nat ->
    real_lt (real_mult a (real_pow kappa (Nat.min p q))) eps).
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps) as [N HN].
  exists N.
  intros p q Hpq.
  exact (geo_tail_budget kappa a eps Hk1 Hk2 Ha Heps p q N Hpq HN).
Qed.

(* ============ 8. 提取探针（可执行 OCaml，G3 关卡） ============ *)
Set Warnings "-extraction-opaque-accessed".
Extraction "upbudgetreal.ml" r_arch_pow_real budget_cond_sufficient geo_tail_budget budget_min_tail.

End BudgetReal.

(* ---------- UpArchAttn ---------- *)
From Stdlib Require Import QArith.QArith.
Import BudgetReal.

(* ============================================================ *)
(* UpArchAttn.v —— 榜 A3：r_arch_pow_attn 的 Real 层镜像            *)
(*                                                              *)
(* 扫描件背景（分析-219平凡定理热点扫描-20260907.md 榜 A3）：        *)
(*   根文件 CW_ConstructiveWorld_219.v 注意力收敛区 L29247 的接口前提 *)
(*     Variable r_arch_pow_attn :                                *)
(*       forall (a : R), lt zero a -> forall eps : R, lt zero eps -> *)
(*         sigT (fun N : nat =>                                  *)
(*           lt (mult a (r_pow (minus one delta) N)) eps),        *)
(*   是几何击破假设 attention_iterate_converges（L29330）的 N 供给口。 *)
(*   它与收敛区已升级的 r_arch_pow（ConvergenceCauchy L14081）同构，  *)
(*   却从未连接到已验收的 Real 层预算机器 UpBudgetReal.r_arch_pow_real *)
(*   （0<κ<1、0<a、0<eps 时 sigT N, a·κ^N < eps）。本文件消除该断连： *)
(*                                                              *)
(* 件 1（主件）r_arch_pow_attn_real：接口前提在具体 Real 层的实例化。 *)
(*   形态对齐映射（探针结论）：                                    *)
(*     R（抽象，RealInterfaceEnhanced 实例参数）                  *)
(*         ⟿ Real（柯西实数 sigT (u : Qseq) (cauchy u)） *)
(*     lt zero / lt ⟿ real_lt real_zero / real_lt（Type 版）       *)
(*     mult ⟿ real_mult                                          *)
(*     minus one delta ⟿ real_plus real_one (real_opp delta)      *)
(*       （Real 层无减法记号，x−y := x+(−y)，同根 L41051 惯例）      *)
(*     r_pow（根 L14071 Fixpoint：O ↦ one, S m ↦ mult x (pow x m)， *)
(*       左乘形态）⟿ real_pow（UpBudgetReal L46 Fixpoint：          *)
(*       O ↦ real_one, S m ↦ real_mult x (pow x m)——同为左乘形态，   *)
(*       定义同构确认：桥为定义级实例化（根 r_pow 活在抽象 R 世界，   *)
(*       跨世界 real_eq 桥不可类型化；UpBudgetReal 已设 Notation      *)
(*       r_pow := real_pow，接口名与函数在 Real 层合一）。           *)
(*     Section Variable delta/delta_pos/delta_lt_one（闭合后消失）  *)
(*         ⟿ 语句显式前提。                                       *)
(*                                                              *)
(* 件 2（组装预演）attention_iterate_converges_real：              *)
(*   消费件 1 + 根 attention_tv_iter_contraction（L29287）结论的     *)
(*   Real 镜像链 tv_n ≤ (1−δ)^n·tv_0（根 r_pow_dec_iter_attn 的     *)
(*   Real 镜像即 UpBudgetReal.real_pow_anti_mono，直接复用），       *)
(*   给出 sigT 预算 N 见证定理。覆盖面注记：根定理的语义对象        *)
(*   attention_step/tv_dist/boltzmann_dist_attn 生活在抽象 Section  *)
(*   世界，其实例化需在 Real 层整体放电 detailed_balance/           *)
(*   minorization/sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等 *)
(*   接口前提（天级工程，不属本小件）；按任务书条款以 Real 序列       *)
(*   tv_seq := n ↦ TV(iterate n μ₀, p_b) 承载最小骨架，每步几何      *)
(*   收缩作为镜像前提 Hstep 显式列出。主件 1 不受影响。              *)
(*                                                              *)
(* 纪律：纯构造性；Set 层语句（real_lt/real_le/real_eq/sigT）；      *)
(*       全部 Qed 闭合；只消费根内/UpBudgetReal 已证机器。           *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============ 1. 1−δ 的 Real 层序引理（κ := 1−δ 良定前提） ============ *)

(* 根 L14270 one_minus_kappa_pos 的 Real 镜像：δ < 1 ⟹ 0 < 1−δ *)
Lemma one_minus_delta_pos_real : forall delta : Real,
  real_lt delta real_one ->
  real_lt real_zero (real_plus real_one (real_opp delta)).
Proof.
  intros delta Hd. exact (real_lt_opp_plus delta real_one Hd).
Qed.

(* 根注意力区前提的对称支 Real 镜像：0 < δ ⟹ 1−δ < 1
   （逐点差零 + real_lt_eq_lt：1−(1−δ) == δ 逐点 ring） *)
Lemma one_minus_delta_lt_one_real : forall delta : Real,
  real_lt real_zero delta ->
  real_lt (real_plus real_one (real_opp delta)) real_one.
Proof.
  intros delta Hd.
  apply (real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one).
  apply (real_lt_eq_lt real_zero delta).
  - exact Hd.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n.
    rewrite (real_plus_proj real_one
               (real_opp (real_plus real_one (real_opp delta))) n).
    rewrite (real_opp_proj (real_plus real_one (real_opp delta)) n).
    rewrite (real_plus_proj real_one (real_opp delta) n).
    rewrite (real_opp_proj delta n).
    cbn [projT1].
    ring.
Qed.

(* ============ 2. 件 1 主件：接口前提的 Real 层实例化 ============ *)

Theorem r_arch_pow_attn_real :
  forall delta : Real, real_lt real_zero delta -> real_lt delta real_one ->
  forall a : Real, real_lt real_zero a ->
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
              (real_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (r_arch_pow_real (real_plus real_one (real_opp delta))
           (one_minus_delta_pos_real delta Hd2)
           (one_minus_delta_lt_one_real delta Hd1)
           a Ha eps Heps).
Qed.

(* ============ 3. 件 2 组装预演：TV 几何衰减链（Real 镜像） ============ *)

(* 根 attention_tv_iter_contraction（L29287）结论的 Real 镜像链：
   每步 tv_{n+1} ≤ (1−δ)·tv_n ⟹ tv_n ≤ (1−δ)^n·tv₀。
   （根 r_pow_dec_iter_attn 的幂反单调 Real 镜像即
     UpBudgetReal.real_pow_anti_mono，件 2 主定理直接复用，不重证。） *)
Lemma tv_iter_decay_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (real_plus real_one (real_opp delta)) n)
                       (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  assert (Hk1 : real_lt real_zero (real_plus real_one (real_opp delta)))
    by exact (one_minus_delta_pos_real delta Hd2).
  set (kappa := real_plus real_one (real_opp delta)) in *.
  induction n as [| n IH].
  - (* κ^0 ≡ one：1·tv₀ == tv₀ *)
    apply real_eq_le_bridge.
    apply real_eq_sym.
    exact (real_mult_one_l (tv_seq Datatypes.O)).
  - (* tv_{n+1} ≤ κ·tv_n ≤ κ·(κ^n·tv₀) == κ^{n+1}·tv₀ *)
    apply (real_le_trans _ (real_mult kappa (tv_seq n))).
    + exact (Hstep n).
    + apply (real_le_trans _ (real_mult (tv_seq n) kappa)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm kappa (tv_seq n)).
      * apply (real_le_trans _
                 (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                            kappa)).
        -- exact (real_le_mult_compat (tv_seq n)
                    (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                    kappa Hk1 IH).
        -- apply real_eq_le_bridge.
           exact (real_eq_trans
                    (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                               kappa)
                    (real_mult kappa
                               (real_mult (real_pow kappa n) (tv_seq Datatypes.O)))
                    (real_mult (real_mult kappa (real_pow kappa n))
                               (tv_seq Datatypes.O))
                    (real_mult_comm (real_mult (real_pow kappa n)
                                        (tv_seq Datatypes.O))
                                    kappa)
                    (real_mult_assoc kappa (real_pow kappa n)
                                     (tv_seq Datatypes.O))).
Qed.

(* ============ 4. 件 2 主定理：迭代收敛的 sigT 显式预算见证 ============ *)

(* 根 attention_iterate_converges（L29330）的 Real 层镜像组装：
   预算 N 由件 1（r_arch_pow_attn_real）构造；尾界 n ≥ N 由
   tv 衰减链（本文件件 2 前置）+ 幂反单调（real_pow_anti_mono）
   + 件 1 的 a·κ^N < eps 放电。
   覆盖面注记：tv_seq 即根语义对象 n ↦ TV(iterate attention_step n μ₀,
   boltzmann_dist_attn) 的 Real 承载；每步收缩 Hstep 对应根
   attention_tv_contraction 的结论形态。根抽象 Section 的完整
   Real 层实例化需整体放电 detailed_balance/minorization/
   sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat 对等接口前提，
   天级工程，不属本小件（主件 1 不受影响）。 *)
Theorem attention_iterate_converges_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt real_zero (tv_seq Datatypes.O) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2
             (tv_seq Datatypes.O) Htv0 eps Heps) as [N HN].
  exists N.
  intros n Hn.
  set (kappa := real_plus real_one (real_opp delta)) in *.
  apply (real_le_lt_trans _
           (real_mult (real_pow kappa n) (tv_seq Datatypes.O))).
  - exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans _
             (real_mult (real_pow kappa N) (tv_seq Datatypes.O))).
    + assert (Hk1 : real_lt real_zero kappa)
        by exact (one_minus_delta_pos_real delta Hd2).
      assert (Hk2le : real_le kappa real_one)
        by exact (real_lt_le_bridge kappa real_one
                    (one_minus_delta_lt_one_real delta Hd1)).
      assert (Hanti : real_le (real_pow kappa n) (real_pow kappa N))
        by exact (real_pow_anti_mono kappa Hk1 Hk2le N n Hn).
      exact (real_le_mult_compat (real_pow kappa n) (real_pow kappa N)
               (tv_seq Datatypes.O) Htv0 Hanti).
    + exact (real_eq_lt_lt (real_mult (real_pow kappa N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow kappa N)) eps
               (real_mult_comm (real_pow kappa N) (tv_seq Datatypes.O)) HN).
Qed.

(* ============ 5. 提取探针（G3：零 Obj.magic） ============ *)

Extraction "uparchattn.ml" r_arch_pow_attn_real attention_iterate_converges_real.

(* ---------- UpConstitution ---------- *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import BudgetReal.
Set Extraction Output Directory ".".
Module Constitution.
(* ============================================================ *)
(* UpConstitution.v —— ASI 资源宪法：改进声明的 Set 层类型与可判定验证器 *)
(*                                                              *)
(* 理论来源：成果存档/新算法.txt 推导 3「无见证的无限承诺不合法」    *)
(*   ——自我改进系统的每一次改进声明必须输出 (κ, N, 击穿见证) 三元组；  *)
(*   这不是软约束：本文件给出可机器检查的宪法执行器。               *)
(*                                                              *)
(* 五件交付：                                                    *)
(*   件 1  claim_decl        改进声明的 Set 层 Record 类型          *)
(*   件 2  check_claim       可判定验证器（Defined 可执行，四门六证）  *)
(*   件 3  valid_claim_yields_breakthrough                        *)
(*                          验证器通过 ⟹ 击穿见证存在（健全性）      *)
(*   件 4  invalid_claim_counter_*                               *)
(*                          具体反例精确判定（可反驳性·E 模式）      *)
(*   件 5  claim_chain       两条有效声明的复合仍有效（宪法闭合）     *)
(*                                                              *)
(* 数学核心（nat/Q 层自足，不依赖 Real 层）：                       *)
(*   uc_bernoulli        (1+c)^n ≥ 1 + n·c 的 Q 形 Bernoulli       *)
(*   uc_growth_breaks    Q 层阿基米德击穿（Qarchimedean + 正 nat 预算）*)
(*   q_decay_breaks      Q 层几何衰减击穿 = r_arch_pow_real 的       *)
(*                       Q 层自足对应件（κ∈(0,1) ⟹ 有限预算存在）    *)
(*                                                              *)
(* 层位纪律：宪法面语句全 Set 层（QleT'/QltT/NatLe/Id/sigT/And/Or）；*)
(*   内部代数微件沿 LCAudit 先例口径（Qle/== 前提位）；  *)
(*   纯构造性：禁词零出现（见交付报告 G1）；全部 Qed 闭合。           *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 件 1：改进声明的 Set 层类型                                 *)
(* ============================================================ *)
(* 形态裁决：任务书草案把 QleT/QltT 证挤进 sigT 类型，使 κ≥1 的声明   *)
(* 不可构造——与件 4「构造具体反例声明」直接冲突（反例必须可构造才能   *)
(* 被验证器拒收）。故裁决为：无约束 Record + 验证器判定。            *)
(* 语义：每步按 (1−κ) 收缩基线 c0，声明 N 步内严格跨过阈值 eps。      *)

Record claim_decl : Set := mk_claim {
  cl_c0 : Q;        (* 当前基线值 c0 *)
  cl_eps : Q;       (* 目标阈值 eps *)
  cl_kappa : Q;     (* 声明改进率 κ *)
  cl_N : nat;       (* 声明到达预算 N *)
  cl_id : nat       (* 声明 id *)
}.

(* ============================================================ *)
(* §1 Q 层代数微件（桥与换形；LCAudit 先例口径）                    *)
(* ============================================================ *)

Lemma uc_qeq_le : forall x y : Q, x == y -> Qle x y.
Proof. intros x y H. rewrite H. apply Qle_refl. Qed.

Lemma uc_qeq_le_l : forall x y z : Q, x == y -> Qle x z -> Qle y z.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

Lemma uc_qeq_le_r : forall x y z : Q, x == y -> Qle z x -> Qle z y.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

Lemma uc_qeq_lt_l : forall x y z : Q, x == y -> Qlt x z -> Qlt y z.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

Lemma uc_qeq_lt_r : forall x y z : Q, x == y -> Qlt z x -> Qlt z y.
Proof. intros x y z H H0. rewrite H in H0. exact H0. Qed.

(* 倒数正性（Q 层自足版；三分判定构造性收尾） *)
Lemma uc_inv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (1 / x).
Proof.
intros x Hx.
destruct (Q_dec 0 (1 / x)) as [[H | H] | H].
- exact H.
- exfalso.
  assert (Hle : (1 / x) * x <= 0 * x).
  { apply (Qmult_le_compat_r (1 / x) 0 x).
    - apply (Qlt_le_weak (1 / x) 0). exact H.
    - apply (Qlt_le_weak 0 x). exact Hx. }
  assert (Hone : (1 / x) * x == 1).
  { field. intro Hz. rewrite Hz in Hx. exact (Qlt_irrefl 0%Q Hx). }
  rewrite Hone in Hle.
  assert (Hlt0 : Qlt 0 (0 * x)).
  { apply (Qlt_le_trans 0%Q 1%Q (0 * x)).
    - unfold Qlt. simpl. lia.
    - exact Hle. }
  apply (Qlt_irrefl 0%Q).
  apply (uc_qeq_lt_r (0 * x) 0%Q 0%Q).
  + ring.
  + exact Hlt0.
- exfalso.
  assert (Hle : (1 / x) * x <= 0 * x).
  { apply (Qmult_le_compat_r (1 / x) 0 x).
    - apply (uc_qeq_le (1 / x) 0%Q (Qeq_sym _ _ H)).
    - apply (Qlt_le_weak 0 x). exact Hx. }
  assert (Hone : (1 / x) * x == 1).
  { field. intro Hz. rewrite Hz in Hx. exact (Qlt_irrefl 0%Q Hx). }
  rewrite Hone in Hle.
  assert (Hlt0 : Qlt 0 (0 * x)).
  { apply (Qlt_le_trans 0%Q 1%Q (0 * x)).
    - unfold Qlt. simpl. lia.
    - exact Hle. }
  apply (Qlt_irrefl 0%Q).
  apply (uc_qeq_lt_r (0 * x) 0%Q 0%Q).
  + ring.
  + exact Hlt0.
Qed.

(* 序的加 −x 换形 *)
Lemma uc_le_opp_shift : forall x y : Q, Qle x y -> Qle 0 (y + - x).
Proof.
intros x y H. apply (Qle_trans _ (x + - x) _).
- apply uc_qeq_le. ring.
- apply Qplus_le_compat.
  + exact H.
  + apply Qle_refl.
Qed.

Lemma uc_lt_opp_shift : forall x y : Q, Qlt x y -> Qlt 0 (y + - x).
Proof.
intros x y H.
assert (Hmid : Qlt ((- x) + x) ((- x) + y)).
{ apply (proj2 (Qplus_lt_r x y (- x))). exact H. }
apply (uc_qeq_lt_r ((- x) + y) (y + - x) 0%Q).
- ring.
- apply (uc_qeq_lt_l ((- x) + x) 0%Q ((- x) + y)).
  + ring.
  + exact Hmid.
Qed.

Lemma uc_lt_minus_inv : forall x y : Q, Qlt 0 (y + - x) -> Qlt x y.
Proof.
intros x y H.
assert (Hmid : Qlt (x + 0) (x + (y + - x))).
{ apply (proj2 (Qplus_lt_r 0 (y + - x) x)). exact H. }
apply (uc_qeq_lt_r (x + (y + - x)) y x).
- ring.
- apply (uc_qeq_lt_l (x + 0) x (x + (y + - x))).
  + ring.
  + exact Hmid.
Qed.

Lemma uc_opp_le_shift : forall x : Q, Qle 0 x -> Qle (- x) 0.
Proof.
intros x H. apply (Qle_trans _ ((- x) + x) _).
- apply (uc_qeq_le_l ((- x) + 0) (- x) ((- x) + x)).
  + ring.
  + apply Qplus_le_compat.
    * apply Qle_refl.
    * exact H.
- apply (uc_qeq_le_r ((- x) + x) 0%Q ((- x) + x)).
  + ring.
  + apply Qle_refl.
Qed.

(* 乘法右消去（严格版；Q_dec 三分构造性收尾） *)
Lemma uc_cancel_lt_r : forall a b p : Q,
  Qlt 0 p -> QltT (a * p) (b * p) -> QltT a b.
Proof.
intros a b p Hp Hlt. apply QltT_to_Qlt in Hlt.
destruct (Q_dec a b) as [[H1 | H2] | H3].
- apply Qlt_to_QltT. exact H1.
- exfalso. apply (Qlt_irrefl (b * p)).
  apply (Qlt_trans (b * p) (a * p) (b * p)).
  + apply (Qmult_lt_compat_r b a p Hp H2).
  + exact Hlt.
- exfalso. apply (Qlt_irrefl (a * p)).
  rewrite <- H3 in Hlt. exact Hlt.
Qed.

(* ============================================================ *)
(* §2 q_pow 幂代数（消费 q_pow）                      *)
(* ============================================================ *)

Lemma uc_pow_eq_compat : forall (x y : Q) (n : nat), x == y -> q_pow x n == q_pow y n.
Proof.
intros x y n Hxy. induction n as [| n IH]; simpl.
- reflexivity.
- rewrite IH. rewrite Hxy. reflexivity.
Qed.

Lemma uc_pow_add : forall (x : Q) (p q : nat),
  q_pow x (p + q)%nat == q_pow x p * q_pow x q.
Proof.
intros x p q. induction p as [| p IH]; simpl.
- ring.
- rewrite IH. ring.
Qed.

Lemma uc_pow_mul : forall (x y : Q) (n : nat),
  q_pow (x * y) n == q_pow x n * q_pow y n.
Proof.
intros x y n. induction n as [| n IH]; simpl.
- reflexivity.
- rewrite IH. ring.
Qed.

Lemma uc_pow_inv_pair : forall (a b : Q) (n : nat),
  a * b == 1 -> q_pow a n * q_pow b n == 1.
Proof.
intros a b n Hab. induction n as [| n IH]; simpl.
- reflexivity.
- assert (Hre : (a * q_pow a n) * (b * q_pow b n)
              == (a * b) * (q_pow a n * q_pow b n)) by ring.
  rewrite Hre. rewrite Hab. rewrite IH. reflexivity.
Qed.

(* 衰减指数下降：0 ≤ x ≤ 1 ⟹ x^(p+q) ≤ x^p（sc_qpow_dec 迭代） *)
Lemma uc_pow_le_drop : forall (x : Q) (p q : nat),
  Qle 0 x -> Qle x 1 -> Qle (q_pow x (p + q)%nat) (q_pow x p).
Proof.
intros x p q Hx0 Hx1. induction q as [| q IH].
- replace (p + 0)%nat with p by lia. apply Qle_refl.
- replace (p + Datatypes.S q)%nat with (Datatypes.S (p + q)) by lia.
  apply (Qle_trans _ (q_pow x (p + q)%nat) _).
  + apply (sc_qpow_dec x (p + q)%nat Hx0 Hx1).
  + exact IH.
Qed.

(* ============================================================ *)
(* §3 Q 形 Bernoulli：(1+c)^n ≥ 1 + n·c（c ≥ 0）                  *)
(* ============================================================ *)

Lemma uc_znat_pos : forall n : nat, Qle 0 (Z.of_nat n # 1).
Proof. intro n. unfold Qle. simpl. lia. Qed.

Lemma uc_bernoulli : forall (c : Q) (n : nat),
  QleT' 0 c -> QleT' (1 + (Z.of_nat n # 1) * c) (q_pow (1 + c) n).
Proof.
intros c n HcT. pose proof (QleT'_to_Qle 0 c HcT) as Hc.
induction n as [| n IH].
- apply Qle_to_QleT'.
  replace (q_pow (1 + c) 0) with 1%Q by reflexivity.
  apply uc_qeq_le.
  replace (Z.of_nat 0 # 1) with (0 # 1)%Q by reflexivity.
  ring.
- apply Qle_to_QleT'.
  assert (Hs : (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + 1).
  { unfold Qeq. simpl. lia. }
  apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c) _).
  + apply uc_qeq_le. rewrite Hs. ring.
  + apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) * (1 + c)) _).
    * (* (1 + n·c) + c ≤ (1+n·c)·(1+c)：差项 n·c·c ≥ 0 *)
      apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c + (Z.of_nat n # 1) * c * c) _).
      -- apply (Qle_trans _ ((1 + (Z.of_nat n # 1) * c) + c + 0) _).
         ++ apply uc_qeq_le. ring.
         ++ apply Qplus_le_compat.
            ** apply Qle_refl.
            ** (* 0 ≤ (n#1·c)·c *)
               apply (Qle_trans _ (0 * c)%Q _).
               { apply uc_qeq_le. ring. }
               { pose proof (uc_znat_pos n) as Hzn.
                 assert (Hzc : Qle 0 ((Z.of_nat n # 1) * c)).
                 { apply (Qle_trans _ (0 * c)%Q _).
                   - apply uc_qeq_le. ring.
                   - apply (Qmult_le_compat_r 0 (Z.of_nat n # 1) c Hzn Hc). }
                 apply (Qle_trans _ (0 * c)%Q _).
                 - apply uc_qeq_le. ring.
                 - apply (Qmult_le_compat_r 0 ((Z.of_nat n # 1) * c) c Hzc Hc). }
      -- apply uc_qeq_le. ring.
    * (* (1+c) 单调放大（0 ≤ 1+c） *)
      rewrite (q_pow_succ (1 + c) n).
      rewrite (Qmult_comm (1 + c) (q_pow (1 + c) n)).
      apply (Qmult_le_compat_r (1 + (Z.of_nat n # 1) * c) (q_pow (1 + c) n) (1 + c)
               (QleT'_to_Qle _ _ IH)).
      apply (Qle_trans _ 1%Q _).
      -- unfold Qle. simpl. lia.
      -- apply (uc_qeq_le_l (1 + 0) 1 (1 + c)).
         ++ ring.
         ++ apply Qplus_le_compat.
            ** apply Qle_refl.
            ** exact Hc.
Qed.

(* ============================================================ *)
(* §4 Q 层阿基米德击穿：真增长率必有正预算（Qarchimedean + Bernoulli）*)
(* ============================================================ *)

Lemma uc_growth_breaks : forall (c T : Q),
  Qlt 0 c -> Qlt 0 T ->
  sigT (fun N => And (NatLe 1 N) (QltT T (q_pow (1 + c) N))).
Proof.
intros c T Hc HT.
destruct (Qarchimedean (T / c)) as [p Hp].
exists (Datatypes.S (Pos.to_nat p)).
split.
- apply NatLe_lift. lia.
- apply Qlt_to_QltT.
  assert (Hconv : Z.of_nat (Pos.to_nat p) = Z.pos p) by (apply positive_nat_Z).
  assert (Hconv2 : Z.of_nat (Datatypes.S (Pos.to_nat p)) = (Z.pos p + 1)%Z) by lia.
  assert (Hid : (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) == (Z.pos p # 1) + 1).
  { rewrite Hconv2. unfold Qeq. simpl. lia. }
  assert (Hcancel : (T / c) * c == T).
  { field. intro Hz. rewrite Hz in Hc. exact (Qlt_irrefl 0%Q Hc). }
  assert (H0 : (T / c) * c < (Z.pos p # 1) * c).
  { apply (Qmult_lt_compat_r (T / c) (Z.pos p # 1) c Hc Hp). }
  rewrite Hcancel in H0.
  assert (H1 : (Z.pos p # 1) * c < (Z.pos p # 1) * c + c).
  { apply (uc_qeq_lt_l ((Z.pos p # 1) * c + 0) ((Z.pos p # 1) * c) ((Z.pos p # 1) * c + c)).
    - ring.
    - apply (proj2 (Qplus_lt_r 0%Q c ((Z.pos p # 1) * c))). exact Hc. }
  assert (H2 : (Z.pos p # 1) * c + c
             == (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { rewrite Hid. ring. }
  assert (H3 : T < (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { apply (Qlt_trans T ((Z.pos p # 1) * c) _).
    - exact H0.
    - apply (uc_qeq_lt_r _ _ _ H2). exact H1. }
  assert (H4 : T < 1 + (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c).
  { apply (Qlt_trans T ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c) _).
    - exact H3.
    - apply (uc_qeq_lt_r ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 1)
                         (1 + (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c)).
      + ring.
      + apply (uc_qeq_lt_l ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 0)
                           ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c)
                           ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c + 1)).
        * ring.
        * apply (proj2 (Qplus_lt_r 0%Q 1%Q
                          ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1) * c))).
          unfold Qlt. simpl. lia. }
  pose proof (QleT'_to_Qle _ _
    (uc_bernoulli c (Datatypes.S (Pos.to_nat p))
       (Qle_to_QleT' 0 c (Qlt_le_weak 0 c Hc)))) as Hb.
  apply (Qlt_le_trans _ _ _ H4 Hb).
Qed.

(* ============================================================ *)
(* §5 Q 层几何衰减击穿（r_arch_pow_real 的 Q 层自足对应件）          *)
(*   κ∈(0,1)、c0>0、eps>0 ⟹ 存在正预算 N 使 c0·(1−κ)^N < eps        *)
(*   预算 N 的显式形态：Qarchimedean 在 c0/eps 除以 κ/(1−κ) 上解出。  *)
(* ============================================================ *)

Theorem q_decay_breaks : forall (k c0 eps : Q),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => And (NatLe 1 N) (QltT (c0 * q_pow (1 - k) N) eps)).
Proof.
intros k c0 eps HkT0 HkT1 Hc0T HeT.
pose proof (QltT_to_Qlt 0 k HkT0) as Hk0.
pose proof (QltT_to_Qlt k 1 HkT1) as Hk1.
pose proof (QltT_to_Qlt 0 c0 Hc0T) as Hc0.
pose proof (QltT_to_Qlt 0 eps HeT) as He.
assert (H1k : Qlt 0 (1 - k)) by (apply (uc_lt_opp_shift k 1 Hk1)).
assert (Hinv : Qlt 0 (1 / (1 - k))) by (apply (uc_inv_pos (1 - k) H1k)).
assert (Hg : 1 / (1 - k) == 1 + k / (1 - k)).
{ field. intro Hz. rewrite Hz in H1k. exact (Qlt_irrefl 0%Q H1k). }
assert (HkcLt : Qlt 0 (k / (1 - k))).
{ apply (uc_qeq_lt_r (k * (1 / (1 - k))) (k / (1 - k)) 0%Q).
  - unfold Qdiv. ring.
  - apply (Qmult_lt_0_compat k (1 / (1 - k)) Hk0 Hinv). }
assert (Ht : Qlt 0 (c0 / eps)).
{ apply (uc_qeq_lt_r (c0 * (1 / eps)) (c0 / eps) 0%Q).
  - unfold Qdiv. ring.
  - apply (Qmult_lt_0_compat c0 (1 / eps) Hc0 (uc_inv_pos eps He)). }
destruct (uc_growth_breaks (k / (1 - k)) (c0 / eps) HkcLt Ht) as [N [HN1 HN]].
exists N. split.
- exact HN1.
- pose proof (QltT_to_Qlt (c0 / eps) (q_pow (1 + k / (1 - k)) N) HN) as HN'.
  assert (Hpow : q_pow (1 / (1 - k)) N == q_pow (1 + k / (1 - k)) N)
    by (apply uc_pow_eq_compat; exact Hg).
  assert (Hcancel2 : (c0 / eps) * eps == c0).
  { field. intro Hz. rewrite Hz in He. exact (Qlt_irrefl 0%Q He). }
  assert (Hstep : (c0 / eps) * eps < eps * q_pow (1 + k / (1 - k)) N).
  { rewrite (Qmult_comm eps (q_pow (1 + k / (1 - k)) N)).
    apply (Qmult_lt_compat_r (c0 / eps) (q_pow (1 + k / (1 - k)) N) eps He HN'). }
  rewrite Hcancel2 in Hstep.
  assert (Hmul : c0 < eps * q_pow (1 / (1 - k)) N).
  { apply (uc_qeq_lt_r (eps * q_pow (1 + k / (1 - k)) N)
                       (eps * q_pow (1 / (1 - k)) N) c0).
    - rewrite Hpow. reflexivity.
    - exact Hstep. }
  assert (Hpair : q_pow (1 - k) N * q_pow (1 / (1 - k)) N == 1).
  { apply uc_pow_inv_pair.
    field. intro Hz. rewrite Hz in H1k. exact (Qlt_irrefl 0%Q H1k). }
  assert (HposGN : Qlt 0 (q_pow (1 / (1 - k)) N))
    by (apply (sc_qpow_pos N (1 / (1 - k)) Hinv)).
  apply (uc_cancel_lt_r (c0 * q_pow (1 - k) N) eps (q_pow (1 / (1 - k)) N) HposGN).
  apply Qlt_to_QltT.
  apply (uc_qeq_lt_l c0
           ((c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N)
           (eps * q_pow (1 / (1 - k)) N)).
  { assert (Hre : (c0 * q_pow (1 - k) N) * q_pow (1 / (1 - k)) N
                == c0 * (q_pow (1 - k) N * q_pow (1 / (1 - k)) N)) by ring.
    rewrite Hre. rewrite Hpair. rewrite Qmult_1_r. reflexivity. }
  { exact Hmul. }
Qed.

(* ============================================================ *)
(* §6 件 2：可判定验证器（Defined 可执行）                          *)
(*   六个单门判定器：bool 判定 + 依赖 match 同步发放 Set 层证书；      *)
(*   拒绝时发拒绝码（可反驳性：负向判定同样精确）。                   *)
(* ============================================================ *)

(* 拒绝码（E 模式：反例与陈述同权，负向判定携带可机器检查的理由） *)
Inductive claim_reject : Set :=
| rj_kappa   (* kappa 不在 [0,1)：零衰减捷径或负率 *)
| rj_budget  (* N = 0：即时报达声明 *)
| rj_data    (* c0 < 0 或 eps <= 0：基线/阈值不合法 *)
| rj_reach.  (* 预算 N 内不跨阈值：无见证承诺 *)

(* 通过证书：六证包（每门一张 Id 型 Set 层证） *)
Definition claim_pass (cl : claim_decl) : Set :=
  And (And (QleT' 0 (cl_kappa cl)) (QltT (cl_kappa cl) 1))
      (And (NatLe 1 (cl_N cl))
           (And (And (QleT' 0 (cl_c0 cl)) (QltT 0 (cl_eps cl)))
                (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl))
                      (cl_eps cl)))).

(* 门 1a：0 <= kappa *)
Definition kap_low_dec (cl : claim_decl)
  : Or (QleT' 0 (cl_kappa cl))
       (And (Id (Qle_bool 0 (cl_kappa cl)) false) claim_reject) :=
  match Qle_bool 0 (cl_kappa cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_kappa)
  end.

(* 门 1b：kappa < 1 *)
Definition kap_high_dec (cl : claim_decl)
  : Or (QltT (cl_kappa cl) 1)
       (And (Id (Qlt_bool (cl_kappa cl) 1) false) claim_reject) :=
  match Qlt_bool (cl_kappa cl) 1 as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_kappa)
  end.

(* 门 2：N >= 1 *)
Definition bud_dec (cl : claim_decl)
  : Or (NatLe 1 (cl_N cl))
       (And (Id (Nat.leb 1 (cl_N cl)) false) claim_reject) :=
  match Nat.leb 1 (cl_N cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_budget)
  end.

(* 门 3a：0 <= c0 *)
Definition dat_c0_dec (cl : claim_decl)
  : Or (QleT' 0 (cl_c0 cl))
       (And (Id (Qle_bool 0 (cl_c0 cl)) false) claim_reject) :=
  match Qle_bool 0 (cl_c0 cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_data)
  end.

(* 门 3b：0 < eps *)
Definition dat_eps_dec (cl : claim_decl)
  : Or (QltT 0 (cl_eps cl))
       (And (Id (Qlt_bool 0 (cl_eps cl)) false) claim_reject) :=
  match Qlt_bool 0 (cl_eps cl) as b
        return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_data)
  end.

(* 门 4：到达性——N 步内严格跨阈值 *)
Definition reach_dec (cl : claim_decl)
  : Or (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl)) (cl_eps cl))
       (And (Id (Qlt_bool (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl))
                          (cl_eps cl))
                 false)
            claim_reject) :=
  match Qlt_bool (cl_c0 cl * q_pow (1 - cl_kappa cl) (cl_N cl)) (cl_eps cl)
          as b return Or (Id b true) (And (Id b false) claim_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, rj_reach)
  end.

(* 宪法执行器本体：顺序过六门，全过发证书，首个不过发拒绝码 *)
Definition check_claim (cl : claim_decl) : Or (claim_pass cl) claim_reject :=
  match kap_low_dec cl with
  | inr (_, r) => inr r
  | inl hk0 =>
    match kap_high_dec cl with
    | inr (_, r) => inr r
    | inl hk1 =>
      match bud_dec cl with
      | inr (_, r) => inr r
      | inl hb =>
        match dat_c0_dec cl with
        | inr (_, r) => inr r
        | inl hc0 =>
          match dat_eps_dec cl with
          | inr (_, r) => inr r
          | inl he =>
            match reach_dec cl with
            | inr (_, r) => inr r
            | inl hr => inl (((hk0, hk1), (hb, ((hc0, he), hr))))
            end
          end
        end
      end
    end
  end.

(* 可判定总结报（vm_compute 友好输出形态） *)
Inductive claim_verdict : Set :=
| v_pass : claim_verdict
| v_reject : claim_reject -> claim_verdict.

Definition check_report (cl : claim_decl) : claim_verdict :=
  match check_claim cl with
  | inl _ => v_pass
  | inr r => v_reject r
  end.

(* 判定总全性：任何声明必得裁决 *)
Lemma check_claim_total : forall cl : claim_decl,
  Or (sigT (fun w : claim_pass cl => Id (check_claim cl) (inl w)))
     (sigT (fun r : claim_reject => Id (check_claim cl) (inr r))).
Proof.
intro cl. unfold check_claim.
destruct (kap_low_dec cl) as [hk0|[f0 r0]];
  [ | right; exists r0; reflexivity ];
destruct (kap_high_dec cl) as [hk1|[f1 r1]];
  [ | right; exists r1; reflexivity ];
destruct (bud_dec cl) as [hb|[f2 r2]];
  [ | right; exists r2; reflexivity ];
destruct (dat_c0_dec cl) as [hc0|[f3 r3]];
  [ | right; exists r3; reflexivity ];
destruct (dat_eps_dec cl) as [he|[f4 r4]];
  [ | right; exists r4; reflexivity ];
destruct (reach_dec cl) as [hr|[f5 r5]];
  [ | right; exists r5; reflexivity ].
left. exists (((hk0, hk1), (hb, ((hc0, he), hr)))). reflexivity.
Qed.

(* 证书 ⟹ 验证器判 inl（负向分支携带 bool=false 证据，可被证书证伪消解；
   inl 见证取判定器实际产出——Set 层 Id 不做证明项无关性比较） *)
Lemma check_claim_inl_of_pass : forall (cl : claim_decl),
  claim_pass cl -> sigT (fun w => Id (check_claim cl) (inl w)).
Proof.
intros cl [[hk0 hk1] [hb [[hc0 he] hr]]].
unfold check_claim.
destruct (kap_low_dec cl) as [g0|[f0 r0]].
- destruct (kap_high_dec cl) as [g1|[f1 r1]].
  + destruct (bud_dec cl) as [g2|[f2 r2]].
    * destruct (dat_c0_dec cl) as [g3|[f3 r3]].
      -- destruct (dat_eps_dec cl) as [g4|[f4 r4]].
         ++ destruct (reach_dec cl) as [g5|[f5 r5]].
            ** exists (((g0, g1), (g2, ((g3, g4), g5)))). reflexivity.
            ** exfalso. pose proof (id_trans (id_sym hr) f5) as Hc5. inversion Hc5.
         ++ exfalso. pose proof (id_trans (id_sym he) f4) as Hc4. inversion Hc4.
      -- exfalso. pose proof (id_trans (id_sym hc0) f3) as Hc3. inversion Hc3.
    * exfalso. pose proof (id_trans (id_sym hb) f2) as Hc2. inversion Hc2.
  + exfalso. pose proof (id_trans (id_sym hk1) f1) as Hc1. inversion Hc1.
- exfalso. pose proof (id_trans (id_sym hk0) f0) as Hc0x. inversion Hc0x.
Qed.

(* ============================================================ *)
(* §7 件 3：健全性——验证器通过 ⟹ 击穿见证存在                       *)
(* ============================================================ *)

Theorem valid_claim_yields_breakthrough : forall (cl : claim_decl) (w : claim_pass cl),
  Id (check_claim cl) (inl w) ->
  sigT (fun N' => And (NatLe N' (cl_N cl))
                      (QltT (cl_c0 cl * q_pow (1 - cl_kappa cl) N') (cl_eps cl))).
Proof.
intros cl w Hw. exists (cl_N cl). split.
- apply NatLe_lift. lia.
- destruct w as [[hk0 hk1] [hb [[hc0 he] hr]]]. exact hr.
Qed.

(* 严格证的降格：QltT x y ⟹ QleT' x y（Qle_bool 三分换形） *)
Lemma uc_qle_bool_false_inv : forall x y : Q, Qle_bool x y = false -> QltT y x.
Proof.
intros x y Hf.
apply Qlt_to_QltT.
apply Qnot_le_lt.
intro Hle.
assert (Ht : Qle_bool x y = true).
{ apply (proj2 (Qle_bool_iff x y)). exact Hle. }
rewrite Hf in Ht. discriminate Ht.
Qed.

Lemma uc_qleT_of_ltT : forall x y : Q, QltT x y -> QleT' x y.
Proof.
intros x y H.
destruct (Qle_bool x y) eqn:Eb.
- apply RealSetoid.eq_Id. exact Eb.
- exfalso. apply (Qlt_irrefl y).
  pose proof (uc_qle_bool_false_inv x y Eb) as Hbad.
  pose proof (QltT_to_Qlt y x Hbad) as Hyx.
  pose proof (QltT_to_Qlt x y H) as Hxy.
  exact (Qlt_trans y x y Hyx Hxy).
Qed.

(* 宪法非空洞：真增长率必有可通过验证器的预算（q_decay_breaks 放电） *)
Theorem constitution_nonvacuous : forall (c0 eps k : Q) (i : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => sigT (fun w => Id (check_claim (mk_claim c0 eps k N i)) (inl w))).
Proof.
intros c0 eps k i Hk0 Hk1 Hc0 He.
destruct (q_decay_breaks k c0 eps Hk0 Hk1 Hc0 He) as [N [HN1 HN]].
exists N.
assert (Hp : claim_pass (mk_claim c0 eps k N i)).
{ repeat split.
  - exact (uc_qleT_of_ltT 0 k Hk0).
  - exact Hk1.
  - exact HN1.
  - exact (uc_qleT_of_ltT 0 c0 Hc0).
  - exact He.
  - exact HN. }
pose proof (check_claim_inl_of_pass (mk_claim c0 eps k N i) Hp) as Hw.
destruct Hw as [w Hwin]. exists w. exact Hwin.
Qed.

(* ============================================================ *)
(* §8 件 4：可反驳性——具体反例的精确判定（E 模式）                   *)
(* ============================================================ *)

(* 反例 1：kappa = 1 的零衰减捷径声明（(1-kappa)^N ≡ 0 作弊路径，宪法禁收） *)
Definition claim_bad_kappa1 : claim_decl := mk_claim (8 # 10) (1 # 10) 1 5 11.

(* 反例 2：负率声明 *)
Definition claim_bad_kappaneg : claim_decl :=
  mk_claim (8 # 10) (1 # 10) (-1 # 2) 5 12.

(* 反例 3：N = 0 的即时报达声明 *)
Definition claim_bad_budget : claim_decl :=
  mk_claim (8 # 10) (1 # 10) (1 # 2) 0 13.

(* 反例 4：边界恰不跨阈（1·(1/2)^1 = 1/2 不 < 1/2）——无见证承诺 *)
Definition claim_bad_reach : claim_decl := mk_claim 1 (1 # 2) (1 # 2) 1 14.

Theorem invalid_claim_counter_kappa1 :
  Id (check_report claim_bad_kappa1) (v_reject rj_kappa).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_kappaneg :
  Id (check_report claim_bad_kappaneg) (v_reject rj_kappa).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_budget :
  Id (check_report claim_bad_budget) (v_reject rj_budget).
Proof. vm_compute. reflexivity. Qed.

Theorem invalid_claim_counter_reach :
  Id (check_report claim_bad_reach) (v_reject rj_reach).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §9 件 5：声明复合——自我改进链的宪法闭合                          *)
(* ============================================================ *)

(* 复合声明：率并集复合 kA+kB-kA*kB，预算相加，接口闸 epsA == c0B *)
Definition chain_claim (A B : claim_decl) : claim_decl :=
  mk_claim (cl_c0 A) (cl_eps B)
           (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B)
           (cl_N A + cl_N B)%nat
           (cl_id A).

Lemma uc_minus_opp : forall x y : Q, x - y == x + (- y).
Proof. intros x y. reflexivity. Qed.

Lemma uc_one_minus_comp : forall kA kB : Q,
  1 - (kA + kB - kA * kB) == (1 - kA) * (1 - kB).
Proof. intros kA kB. unfold Qminus. ring. Qed.

Lemma uc_kappa_comp_le : forall kA kB : Q,
  Qle 0 kA -> Qle 0 kB -> Qlt kB 1 -> Qle 0 (kA + kB - kA * kB).
Proof.
intros kA kB HkA0 HkB0 HkB1.
assert (Hid : kA + kB - kA * kB == kA * (1 - kB) + kB).
{ unfold Qminus. ring. }
apply (uc_qeq_le_r (kA * (1 - kB) + kB) (kA + kB - kA * kB) 0%Q
                   (Qeq_sym _ _ Hid)).
apply (Qle_trans _ (0 + 0)%Q _).
- apply uc_qeq_le. ring.
- apply Qplus_le_compat.
  + apply (Qle_trans _ (0 * (1 - kB)) _).
    * apply uc_qeq_le. ring.
    * apply (Qmult_le_compat_r 0 kA (1 - kB) HkA0).
      apply (uc_le_opp_shift kB 1 (Qlt_le_weak kB 1 HkB1)).
  + exact HkB0.
Qed.

Lemma uc_kappa_comp_lt : forall kA kB : Q,
  Qlt kA 1 -> Qlt kB 1 -> Qlt (kA + kB - kA * kB) 1.
Proof.
intros kA kB HkA1 HkB1.
apply uc_lt_minus_inv.
apply (uc_qeq_lt_r ((1 - kA) * (1 - kB)) (1 + - (kA + kB - kA * kB)) 0%Q).
- exact (Qeq_sym _ _ (uc_one_minus_comp kA kB)).
- apply (Qmult_lt_0_compat (1 - kA) (1 - kB)).
  + apply (uc_lt_opp_shift kA 1 HkA1).
  + apply (uc_lt_opp_shift kB 1 HkB1).
Qed.

(* 复合链到达性：c0 过 A 链跨 epsA、epsA 过 B 链跨 epsB
   ⟹ c0 以复合率在 NA+NB 内跨 epsB *)
Lemma uc_chain_reach : forall (c0 e1 e2 kA kB : Q) (NA NB : nat),
  Qle 0 c0 -> Qle 0 kA -> Qlt kA 1 -> Qle 0 kB -> Qlt kB 1 ->
  QltT (c0 * q_pow (1 - kA) NA) e1 ->
  QltT (e1 * q_pow (1 - kB) NB) e2 ->
  QltT (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat) e2.
Proof.
intros c0 e1 e2 kA kB NA NB Hc0 HkA0 HkA1 HkB0 HkB1 HrA HrB.
pose proof (QltT_to_Qlt (c0 * q_pow (1 - kA) NA) e1 HrA) as HrA'.
pose proof (QltT_to_Qlt (e1 * q_pow (1 - kB) NB) e2 HrB) as HrB'.
pose proof (uc_lt_opp_shift kA 1 HkA1) as H1kA.
pose proof (uc_lt_opp_shift kB 1 HkB1) as H1kB.
assert (Hle1kA : Qle 0 (1 - kA)) by (apply (Qlt_le_weak 0 (1 - kA) H1kA)).
assert (Hle1kB : Qle 0 (1 - kB)) by (apply (Qlt_le_weak 0 (1 - kB) H1kB)).
assert (Hb1kA : Qle (1 - kA) 1).
{ apply (uc_qeq_le_l (1 + - kA) (1 - kA) 1).
  - reflexivity.
  - apply (Qle_trans _ (1 + 0)%Q _).
    + apply Qplus_le_compat; [apply Qle_refl | apply (uc_opp_le_shift kA HkA0)].
    + apply uc_qeq_le. ring. }
assert (Hb1kB : Qle (1 - kB) 1).
{ apply (uc_qeq_le_l (1 + - kB) (1 - kB) 1).
  - reflexivity.
  - apply (Qle_trans _ (1 + 0)%Q _).
    + apply Qplus_le_compat; [apply Qle_refl | apply (uc_opp_le_shift kB HkB0)].
    + apply uc_qeq_le. ring. }
assert (Hcomp : q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat
              == q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat).
{ assert (HcompEq : 1 - (kA + kB - kA * kB) == (1 - kA) * (1 - kB))
    by (apply uc_one_minus_comp).
  rewrite (uc_pow_eq_compat _ _ _ HcompEq).
  rewrite uc_pow_mul.
  rewrite (uc_pow_add (1 - kA) NA NB).
  rewrite (uc_pow_add (1 - kB) NA NB).
  reflexivity. }
assert (HdropA : Qle (q_pow (1 - kA) (NA + NB)%nat) (q_pow (1 - kA) NA))
  by (apply (uc_pow_le_drop (1 - kA) NA NB Hle1kA Hb1kA)).
assert (HdropB : Qle (q_pow (1 - kB) (NA + NB)%nat) (q_pow (1 - kB) NB)).
{ replace (NA + NB)%nat with (NB + NA)%nat by lia.
  apply (uc_pow_le_drop (1 - kB) NB NA Hle1kB Hb1kB). }
assert (Hboth : Qle (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)
                    (q_pow (1 - kA) NA * q_pow (1 - kB) NB)).
{ apply (Qle_trans _ (q_pow (1 - kA) NA * q_pow (1 - kB) (NA + NB)%nat) _).
  - apply (Qmult_le_compat_r (q_pow (1 - kA) (NA + NB)%nat)
                             (q_pow (1 - kA) NA) (q_pow (1 - kB) (NA + NB)%nat)
                             HdropA (q_pow_nonneg (1 - kB) (NA + NB)%nat Hle1kB)).
  - apply (Qle_trans _ (q_pow (1 - kB) (NA + NB)%nat * q_pow (1 - kA) NA) _).
    + apply uc_qeq_le. ring.
    + apply (Qle_trans _ (q_pow (1 - kB) NB * q_pow (1 - kA) NA) _).
      * apply (Qmult_le_compat_r (q_pow (1 - kB) (NA + NB)%nat)
                                 (q_pow (1 - kB) NB) (q_pow (1 - kA) NA)
                                 HdropB (q_pow_nonneg (1 - kA) NA Hle1kA)).
      * apply uc_qeq_le. ring. }
assert (Hmulc : Qle (c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat))
                    (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))).
{ rewrite (Qmult_comm c0 (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)).
  rewrite (Qmult_comm c0 (q_pow (1 - kA) NA * q_pow (1 - kB) NB)).
  apply (Qmult_le_compat_r _ _ c0 Hboth Hc0). }
assert (HposB2 : Qlt 0 (q_pow (1 - kB) NB))
  by (apply (sc_qpow_pos NB (1 - kB) H1kB)).
assert (Hstep1 : c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB)
               < e1 * q_pow (1 - kB) NB).
{ apply (uc_qeq_lt_l
           ((c0 * q_pow (1 - kA) NA) * q_pow (1 - kB) NB)
           (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))
           (e1 * q_pow (1 - kB) NB)).
  - ring.
  - apply (Qmult_lt_compat_r (c0 * q_pow (1 - kA) NA) e1
             (q_pow (1 - kB) NB) HposB2 HrA'). }
assert (HXle : Qle (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
                   (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))).
{ apply (Qle_trans _ (c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat)) _).
  - assert (Hcomp2 : c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat
                   == c0 * (q_pow (1 - kA) (NA + NB)%nat * q_pow (1 - kB) (NA + NB)%nat))
      by (rewrite Hcomp; reflexivity).
    exact (uc_qeq_le _ _ Hcomp2).
  - exact Hmulc. }
apply Qlt_to_QltT.
apply (Qlt_trans
         (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
         (e1 * q_pow (1 - kB) NB) e2).
- apply (Qle_lt_trans
           (c0 * q_pow (1 - (kA + kB - kA * kB)) (NA + NB)%nat)
           (c0 * (q_pow (1 - kA) NA * q_pow (1 - kB) NB))
           (e1 * q_pow (1 - kB) NB)).
  + exact HXle.
  + exact Hstep1.
- exact HrB'.
Qed.

(* 复合定理：两条有效声明接链后，复合声明仍过验证器 *)
Theorem claim_chain : forall (A B : claim_decl) (wA : claim_pass A) (wB : claim_pass B),
  Id (Qeq_bool (cl_eps A) (cl_c0 B)) true ->
  Id (check_claim A) (inl wA) -> Id (check_claim B) (inl wB) ->
  sigT (fun w => Id (check_claim (chain_claim A B)) (inl w)).
Proof.
intros A B wA wB Hface HHA HHB.
destruct wA as [[hk0A hk1A] [hbA [[hc0A heA] hrA]]].
destruct wB as [[hk0B hk1B] [hbB [[hc0B heB] hrB]]].
pose proof (QleT'_to_Qle 0 (cl_kappa A) hk0A) as HkA0.
pose proof (QltT_to_Qlt (cl_kappa A) 1 hk1A) as HkA1.
pose proof (NatLe_drop 1 (cl_N A) hbA) as HbA.
pose proof (QleT'_to_Qle 0 (cl_c0 A) hc0A) as Hc0A.
pose proof (QleT'_to_Qle 0 (cl_kappa B) hk0B) as HkB0.
pose proof (QltT_to_Qlt (cl_kappa B) 1 hk1B) as HkB1.
assert (Hface' : cl_eps A == cl_c0 B).
{ apply (proj1 (Qeq_bool_iff (cl_eps A) (cl_c0 B))).
  apply RealSetoid.Id_eq. exact Hface. }
assert (HrB' : Qlt (cl_eps A * q_pow (1 - cl_kappa B) (cl_N B)) (cl_eps B)).
{ rewrite Hface'. exact (QltT_to_Qlt _ _ hrB). }
assert (Hk0c : QleT' 0 (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B)).
{ apply Qle_to_QleT'.
  apply (uc_kappa_comp_le (cl_kappa A) (cl_kappa B) HkA0 HkB0 HkB1). }
assert (Hk1c : QltT (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B) 1).
{ apply Qlt_to_QltT.
  apply (uc_kappa_comp_lt (cl_kappa A) (cl_kappa B) HkA1 HkB1). }
assert (Hbc : NatLe 1 (cl_N A + cl_N B)%nat).
{ apply NatLe_lift. lia. }
assert (Hreach : QltT
    (cl_c0 A * q_pow (1 - (cl_kappa A + cl_kappa B - cl_kappa A * cl_kappa B))
                     (cl_N A + cl_N B)%nat)
    (cl_eps B)).
{ apply (uc_chain_reach (cl_c0 A) (cl_eps A) (cl_eps B)
           (cl_kappa A) (cl_kappa B) (cl_N A) (cl_N B)
           Hc0A HkA0 HkA1 HkB0 HkB1 hrA (Qlt_to_QltT _ _ HrB')). }
apply (check_claim_inl_of_pass (chain_claim A B)
         (((Hk0c, Hk1c), (Hbc, ((hc0A, heB), Hreach))))).
Qed.

(* ============================================================ *)
(* §10 Real 层对接件（并列形态）：r_arch_pow_real 的预算即             *)
(*     宪法的击穿预算——同一 sigT (fun N => ...) 形状，两套载体        *)
(* ============================================================ *)

Definition real_budget_witness (kappa a eps : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps)
  : sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps) :=
  r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps.

(* ============================================================ *)
(* §11 vm_compute 数值自测（G3 样例输出源）                          *)
(* ============================================================ *)

Definition demo_ok : claim_decl := mk_claim (8 # 10) (1 # 10) (1 # 2) 5 21.
(* c0=4/5, eps=1/10, kappa=1/2, N=5：4/5·(1/2)^5 = 1/40 < 1/10 —— 合法改进声明 *)

Eval vm_compute in check_report demo_ok.
Eval vm_compute in check_report claim_bad_kappa1.
Eval vm_compute in check_report claim_bad_kappaneg.
Eval vm_compute in check_report claim_bad_budget.
Eval vm_compute in check_report claim_bad_reach.

Lemma test_demo_ok_pass : Id (check_report demo_ok) v_pass.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §12 提取探针（G3：Obj.magic = 0）                                *)
(* ============================================================ *)

Set Warnings "-extraction-opaque-accessed".

Extraction "upconstitution.ml" check_claim chain_claim check_report q_pow.

End Constitution.
Import Constitution.

(* ---------- UpProjBPC ---------- *)
(* ============================================================ *)
(* UpProjBPC.v — BPC：KL 区间乘法复合链（席 6 杂交增量）           *)
(*                                                              *)
(* 上游：UpProj.v（抽象投影核母定理，807 行 32 引理，四关全绿）。   *)
(* 本文件在母定理件 1/4 直推半径内，给出封口链经复合掩码的          *)
(* 代价区间端点精确乘法复合：                                     *)
(*   Z_{P1∩P2} == Z1·(Z2|kept1)，其中 Z2|kept1 为 P1 保留集内     *)
(*   二级掩码的条件保留质量（构造性比值形态 Z12·inv Z1）。          *)
(*   代价侧：−log Z12 == (−log Z1) + (−log Zc) 精确分裂，          *)
(*   KL 代价沿封口链可加：KL_{P1}(q) == KL_{P12}(q) + (−log Zc)。  *)
(*                                                              *)
(* 件 4（对照注记，注释级）——四近邻均无 KL 区间乘法链语义：        *)
(*   · PCD 并集界：并集质量重算只给界，无乘法分解恒等式；           *)
(*   · PKI notAfter：时点有效性陈述，无 KL 记账；                  *)
(*   · 级数余项：|S−S_t| ≤ B 型余项界，非端点级精确分裂；           *)
(*   · Doob 塔性质：L2 收敛定理，无可计算证书与代价记账。           *)
(*   本件新度 = 封口点的代数：复合掩码上端点恒等式 + 链式可加。     *)
(*                                                              *)
(* 世界：Real 层 list 世界（UpProj 同款，CW219 根）。              *)
(* 全部 Set 层（Id/And/Or/sigT）；语句零 Prop 泄露；              *)
(* 纯构造性：仅依赖 CW_ConstructiveWorld_219 与 UpProj，           *)
(* 零外部假设；log 正性证书随身（透明 Definition 纪律）。          *)
(* ============================================================ *)


(* ============================================================ *)
(* 顶层助推（Set 层 real_eq 代数小工具，命名前缀 bpc_ 独占）       *)
(* ============================================================ *)

(* −0 == 0（有符号零桥；区间端点 0 形态归零用） *)
Lemma bpc_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  apply (real_eq_trans _ (real_plus (real_opp real_zero) real_zero) _).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_eq_trans _ (real_plus real_zero (real_opp real_zero)) _).
    + apply real_plus_comm.
    + apply real_plus_opp.
Qed.

(* 1·x == x（右单位桥；real_mult_one 是 x·1 形态的镜像） *)
Lemma bpc_one_mult : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* (−t)+t == 0（反序消去零；plus_opp 是 t+(−t) 形态的镜像） *)
Lemma bpc_opp_plus_zero : forall t : Real, real_eq (real_plus (real_opp t) t) real_zero.
Proof.
  intro t.
  apply (real_eq_trans _ (real_plus t (real_opp t)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* 消去律：(a+(−t))+t == a（链式 KL 恒等式的两侧搬移臂） *)
Lemma bpc_cancel_add_opp : forall a t : Real,
  real_eq (real_plus (real_plus a (real_opp t)) t) a.
Proof.
  intros a t.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp t) t)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a real_zero) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp t) t)
               a real_zero).
      * apply real_eq_refl.
      * apply bpc_opp_plus_zero.
    + apply real_plus_zero.
Qed.

(* 加法交换重排：(a+b)+c == (a+c)+b（链式恒等式的中项换位臂） *)
Lemma bpc_assoc_swap : forall a b c : Real,
  real_eq (real_plus (real_plus a b) c) (real_plus (real_plus a c) b).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus b c)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus c b)) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus b c)
               a (real_plus c b)).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply real_plus_assoc.
Qed.

(* 乘法换位：x·(y·z) == y·(x·z)（吸收链的中项重排臂） *)
Lemma bpc_mult_swap : forall x y z : Real,
  real_eq (real_mult x (real_mult y z)) (real_mult y (real_mult x z)).
Proof.
  intros x y z.
  apply (real_eq_trans _ (real_mult (real_mult x y) z) _).
  - apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult (real_mult y x) z) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult x y) z
               (real_mult y x) z).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* ============================================================ *)
(* 母 Section：两级掩码复合（与 UpProj 母 Section 同形扩展）        *)
(*   I/f/idx/f_norm/f_pos 与 UpProj 逐参对齐；P1 P2 两级掩码，     *)
(*   各带非空见证（P1_witness 复用母件 0，P12_witness 复合级）。    *)
(* ============================================================ *)
Section BPChain.

Variable I : Set.                          (* 索引类型（同母） *)
Variable f : I -> Real.                    (* 被投影权重（同母） *)
Variable P1 : I -> bool.                   (* 一级保留谓词 *)
Variable P2 : I -> bool.                   (* 二级保留谓词 *)
Variable idx : list I.                     (* 枚举（同母） *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P1_witness : sigT (fun i : I => And (Id (P1 i) true) (InT i idx)).

(* 复合掩码：P1∩P2（bool 合取） *)
Definition P12 (i : I) : bool := andb (P1 i) (P2 i).

Variable P12_witness : sigT (fun i : I => And (Id (P12 i) true) (InT i idx)).

(* ---------- 质量与证书（透明 Definition：log 证书随身纪律） ------ *)
(* Z1 = 一级保留质量；Z12 = 复合保留质量（即 Z_{P1∩P2}） *)
Definition Z1 : Real := Z_P I f P1 idx.
Definition Z12 : Real := Z_P I f P12 idx.

Definition p1 : real_lt real_zero Z1 := ZP_pos I f P1 idx f_pos P1_witness.
Definition p12 : real_lt real_zero Z12 := ZP_pos I f P12 idx f_pos P12_witness.

(* 条件保留质量 Zc := Z12·inv Z1（= Σ_{P1∧P2} f / Z1，即 Z2|kept1） *)
Definition Zc : Real := real_mult Z12 (real_inv_pos Z1 p1).
(* 正性证书随身（透明，非 Qed 封死） *)
Definition Zc_pos : real_lt real_zero Zc :=
  real_mult_positive Z12 (real_inv_pos Z1 p1) p12 (real_inv_pos_pos Z1 p1).

(* 一级投影核（母形态实例化）与条件质量和的核上形态 *)
Definition Proj1 (i : I) : Real := Proj I f P1 idx f_pos P1_witness i.
Definition Zc_proj1 : Real :=
  real_list_sum I (fun i : I => if P12 i then Proj1 i else real_zero) idx.

(* ---------- 件 1 核 A：点级四支掩码桥 -------------------------- *)
(* P12 支的 Proj1 == P12 支的 f·inv Z1（P1∧P2 保留 ⟹ 一级保留支）； *)
(* P12 逐出支两侧归零。destruct 逐支独立放电，无空 match。          *)
Lemma bpc_pt_bridge : forall y : I,
  real_eq (if P12 y then Proj1 y else real_zero)
          (real_mult (if P12 y then f y else real_zero)
                     (real_inv_pos Z1 p1)).
Proof.
  intro y. unfold P12, Proj1, Proj.
  destruct (P1 y) eqn:H1y; destruct (P2 y) eqn:H2y; cbn [andb].
  - (* true,true：双侧 f·inv Z1，conversion 相等 *)
    apply real_eq_refl.
  - (* true,false：0·inv == 0（sym 转 mult 头，comm + mult_zero） *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,true：0·inv == 0 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,false：0·inv == 0 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
Qed.

(* ---------- 件 1 核 B：两级掩码和的分解（线性提取） ------------- *)
(* Σ_{P12} Proj1 == inv Z1 · Z12：条件质量和（二级掩码在一级投影核  *)
(* 上的和）经逐点桥 + real_list_sum_linear_r 提取线性因子。         *)
Lemma bpc_Zc_proj1_sum : real_eq Zc_proj1
  (real_mult (real_inv_pos Z1 p1) Z12).
Proof.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P12 i then f i else real_zero)
                           (real_inv_pos Z1 p1))
              idx) _).
  - apply (real_list_sum_ext I
             (fun i : I => if P12 i then Proj1 i else real_zero)
             (fun i : I =>
                real_mult (if P12 i then f i else real_zero)
                          (real_inv_pos Z1 p1))
             idx).
    intro y. apply bpc_pt_bridge.
  - apply (real_list_sum_linear_r I (real_inv_pos Z1 p1)
             (fun i : I => if P12 i then f i else real_zero) idx).
Qed.

(* ---------- 复合支配：Z12 ≤ Z1（两级掩码和 ≤ 一级掩码和） ------- *)
Lemma bpc_Z12_le_Z1 : real_le Z12 Z1.
Proof.
  apply (real_list_sum_le I
           (fun i : I => if P12 i then f i else real_zero)
           (fun i : I => if P1 i then f i else real_zero) idx).
  intro y. unfold P12. destruct (P1 y); destruct (P2 y).
  - apply real_le_refl.
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
  - apply real_le_refl.
Qed.

(* ---------- 件 1（主件·乘法分解）：Z12 == Z1·Zc ----------------- *)
(* 纸笔推导：Z1·Zc == Z1·(Z12·inv Z1) == Z12·(Z1·inv Z1)（换位）    *)
(*   == Z12·1 == Z12。核心 = inv 的分配吸收（换位 + inv_correct     *)
(*   + mult_one）；条件占比形态的循环由「Zc 由 Z12/Z1/见证构造、    *)
(*   分解核独立（核 A/B）」排除。                                   *)
Theorem Z_compound_mul : real_eq Z12 (real_mult Z1 Zc).
Proof.
  apply real_eq_sym.
  apply (real_eq_trans _ (real_mult Z1 (real_mult Z12 (real_inv_pos Z1 p1))) _).
  - apply (RealSetoid.real_eq_mult_compat Z1 Zc Z1
             (real_mult Z12 (real_inv_pos Z1 p1))).
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult Z12 (real_mult Z1 (real_inv_pos Z1 p1))) _).
    + apply bpc_mult_swap.
    + apply (real_eq_trans _ (real_mult Z12 real_one) _).
      * apply (RealSetoid.real_eq_mult_compat Z12
                 (real_mult Z1 (real_inv_pos Z1 p1)) Z12 real_one).
        -- apply real_eq_refl.
        -- apply real_inv_pos_correct.
      * apply real_mult_one.
Qed.

(* ---------- 件 1 卫星（语义桥）：条件质量和 == 比值形态 ---------- *)
(* Z2|kept1 的两个构造形态重合：Σ_{P12} Proj1 == Z12·inv Z1。       *)
Lemma bpc_cond_semantics : real_eq Zc_proj1 Zc.
Proof.
  apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) Z12) _).
  - apply bpc_Zc_proj1_sum.
  - unfold Zc. apply real_mult_comm.
Qed.

(* ---------- 复合件 0：条件质量 ∈ (0,1] ------------------------- *)
(* Zc ≤ 1：Zc == Z12·inv Z1 ≤ Z1·inv Z1 == 1（支配 + inv 吸收）。   *)
Theorem Zc_le_one : real_le Zc real_one.
Proof.
  apply (real_le_trans _ (real_mult Z1 (real_inv_pos Z1 p1))).
  - exact (real_le_mult_compat Z12 Z1 (real_inv_pos Z1 p1)
             (real_inv_pos_pos Z1 p1) bpc_Z12_le_Z1).
  - apply (RealSetoid.real_eq_le (real_mult Z1 (real_inv_pos Z1 p1)) real_one).
    apply real_inv_pos_correct.
Qed.

(* ---------- log 复合核：log Z12 == log Z1 + log Zc -------------- *)
(* 端点乘法复合的 log 侧形态；real_log_mult 证书槽与 wd 桥同形       *)
(* （real_mult_positive Z1 Zc p1 Zc_pos，透明证书纪律）。            *)
Lemma bpc_log_Z12_split :
  real_eq (real_log Z12 p12)
          (real_plus (real_log Z1 p1) (real_log Zc Zc_pos)).
Proof.
  apply (real_eq_trans _
           (real_log (real_mult Z1 Zc) (real_mult_positive Z1 Zc p1 Zc_pos)) _).
  - exact (real_log_wd Z12 (real_mult Z1 Zc) p12
             (real_mult_positive Z1 Zc p1 Zc_pos) Z_compound_mul).
  - exact (real_log_mult Z1 Zc p1 Zc_pos).
Qed.

(* ---------- 代价端点乘法复合：−log Z1 + −log Zc == −log Z12 ----- *)
Lemma bpc_cost_mul_split :
  real_eq (real_plus (real_opp (real_log Z1 p1))
                     (real_opp (real_log Zc Zc_pos)))
          (real_opp (real_log Z12 p12)).
Proof.
  apply (real_eq_trans _
           (real_opp (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))) _).
  - apply real_eq_sym. apply real_opp_plus.
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))
             (real_log Z12 p12)).
    apply real_eq_sym. apply bpc_log_Z12_split.
Qed.

(* ---------- 件 2（主件·KL 代价链可加）--------------------------- *)
(* 母定理两次（P1 与 P12）+ 代价端点分裂 + 三臂消元：                *)
(*   A+(−(real_log Z1 p1)) == KLqf == B+(−l12) == B+((−(real_log Z1 p1))+(−lc)) == (B+(−(real_log Z1 p1)))+(−lc) *)
(*   两侧经 (x+(−t))+t 搬移得 A == B+(−lc)。                         *)
(* q 前提诚实给出：归一化 + 逐点正 + 复合掩码兼容（P12 假 ⟹ q=0，    *)
(* 由 andb false 支定义性导出一级兼容，单一前提覆盖两级）。           *)
Theorem proj_kl_chain : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (andb (P1 i) (P2 i)) false -> real_eq (q i) real_zero),
  real_eq (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
          (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                     (real_opp (real_log Zc Zc_pos))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  assert (Hqf1 : forall i : I, Id (P1 i) false -> real_eq (q i) real_zero).
  { intro i. intro Heq1. apply (Hq_fail i).
    exact (projp_id_transport bool false (P1 i)
             (fun b : bool => Id (andb b (P2 i)) false)
             id_refl (id_sym Heq1)). }
  pose proof (proj_kl_cost I f P1 idx f_pos P1_witness q Hq_norm Hq_pos Hqf1) as H1.
  pose proof (proj_kl_cost I f P12 idx f_pos P12_witness q Hq_norm Hq_pos Hq_fail) as H2.
  assert (Hj1 : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                   (real_opp (real_log Z1 p1)))
                        (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))).
  { apply (real_eq_trans _ (KLqf I f idx f_pos q Hq_pos) _).
    - apply real_eq_sym. exact H1.
    - exact H2. }
  assert (Hj2 : real_eq (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))
                        (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                        (real_plus (real_opp (real_log Z1 p1))
                                   (real_opp (real_log Zc Zc_pos)))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Z12 p12))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_plus (real_opp (real_log Z1 p1))
                          (real_opp (real_log Zc Zc_pos)))).
      + apply real_eq_refl.
      + apply real_eq_sym. apply bpc_cost_mul_split.
    - apply real_plus_assoc. }
  assert (Hjoin : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                                (real_opp (real_log Z1 p1)))
                                     (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _ (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                      (real_opp (real_log Z12 p12))) _).
    - exact Hj1.
    - exact Hj2. }
  assert (Hright : real_eq
    (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos)))
               (real_log Z1 p1))
    (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1))) (real_log Z1 p1))
                        (real_opp (real_log Zc Zc_pos))) _) .
    - exact (bpc_assoc_swap (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                       (real_opp (real_log Z1 p1)))
                            (real_opp (real_log Zc Zc_pos)) (real_log Z1 p1)) .
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1))) (real_log Z1 p1))
               (real_opp (real_log Zc Zc_pos))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos))).
      + apply bpc_cancel_add_opp.
      + apply real_eq_refl. }
  apply (real_eq_trans _
           (real_plus (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                 (real_opp (real_log Z1 p1))) (real_log Z1 p1)) _).
  - apply real_eq_sym. apply bpc_cancel_add_opp.
  - apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))
                        (real_log Z1 p1)) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                          (real_opp (real_log Z1 p1))) (real_log Z1 p1)
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos))) (real_log Z1 p1)).
      * exact Hjoin.
      * apply real_eq_refl.
    + exact Hright.
Qed.

(* ---------- 件 3a：封口代价区间端点（质量夹逼）------------------- *)
(* 单侧信息投影版：S ≤ Z12 ≤ S+U（S,U,S+U > 0 的证书前提）⟹          *)
(*   −log(S+U) ≤ −log Z12 ≤ −log S。                                  *)
(* 两端皆定理：log 单调（real_log_le_mono）+ 取负反向                  *)
(* （real_opp_le_compat）；端点乘法复合见 bpc_cost_mul_split。         *)
Theorem proj_cost_interval : forall (S U : Real)
  (HSp : real_lt real_zero S)
  (HUp : real_lt real_zero (real_plus S U))
  (Hlo : real_le S Z12) (Hhi : real_le Z12 (real_plus S U)),
  And (real_le (real_opp (real_log (real_plus S U) HUp))
               (real_opp (real_log Z12 p12)))
      (real_le (real_opp (real_log Z12 p12))
               (real_opp (real_log S HSp))).
Proof.
  intros S U HSp HUp Hlo Hhi.
  split.
  - apply (real_opp_le_compat (real_log Z12 p12)
             (real_log (real_plus S U) HUp)).
    apply (real_log_le_mono Z12 (real_plus S U) p12 HUp).
    exact Hhi.
  - apply (real_opp_le_compat (real_log S HSp) (real_log Z12 p12)).
    apply (real_log_le_mono S Z12 HSp p12).
    exact Hlo.
Qed.

(* ---------- 件 3b：全保留端点（下端点精确值 0）------------------- *)
(* P12 ≡ true ⟹ Z12 == 1（f_norm 桥）⟹ −log Z12 == 0：                *)
(* 封口代价区间 [−log(S_t+U_t), −log S_t] 的 U_t→0 / S_t→1 退化象，    *)
(* 与件 3a 夹逼件在端点处精确闭合。                                   *)
Theorem proj_cost_full_mask_zero :
  (forall i : I, Id (P12 i) true) ->
  real_eq (real_opp (real_log Z12 p12)) real_zero.
Proof.
  intro Hall.
  assert (HZ1 : real_eq Z12 real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P12 i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P12 y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (Hall y)).
    - exact f_norm. }
  assert (Hlog : real_eq (real_log Z12 p12) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact (real_log_wd Z12 real_one p12 real_lt_zero_one HZ1).
    - apply (real_log_one real_lt_zero_one). }
  apply (real_eq_trans _ (real_opp real_zero) _).
  - apply (RealSetoid.real_eq_opp_compat (real_log Z12 p12) real_zero Hlog).
  - apply bpc_opp_zero.
Qed.

End BPChain.

(* ---------- UpEvictId ---------- *)
Module EvictId.
From Stdlib Require Import Extraction.

(* 作用域重指向：EnhancedMod（KLM3 头部 Import 泄漏）的 req 形态代数引理
   与本件 Id 形态同名；此处恢复 219 RealInterface 投影形态。 *)
Local Notation plus_assoc := plus_assoc (only parsing).
Local Notation plus_comm := plus_comm (only parsing).
Local Notation plus_zero := plus_zero (only parsing).
Local Notation plus_opp := plus_opp (only parsing).
Local Notation mult_assoc := mult_assoc (only parsing).
Local Notation mult_comm := mult_comm (only parsing).
Local Notation mult_one := mult_one (only parsing).
Local Notation mult_zero := mult_zero (only parsing).
Local Notation inv_pos_correct := inv_pos_correct (only parsing).
Local Notation le_refl := le_refl (only parsing).
Local Notation le_id_l := le_id_l (only parsing).
Local Notation abs_zero := abs_zero (only parsing).
(* ========================================================================= *)
(* UpEvictId.v — §6 KV 逐出恒等式批（王中王 A1/B3 + A6/B1，2026-09-07）      *)
(*                                                                           *)
(* 本文件以与根 AttentionGibbsBridge 区段同款 Section（变量名/前提形态      *)
(* 逐行对齐）重建逐出世界，交付四组恒等式升级：                              *)
(*                                                                           *)
(* 件 1a  eviction_db_breaking_zero        ：破缺恒为零（拆冗余假设         *)
(*         fluctuation_dissipation_bound 的核心件——本文件全程不使用该      *)
(*         假设；所需前提仅为 Section 自带 detailed_balance）。              *)
(* 件 1b  evicted_boltzmann_steady_exact   ：截断核稳态方程精确成立          *)
(*         （保留因子形态 = 扫描报告 A1 草案逐字）；并列交付全保留特例      *)
(*         evicted_boltzmann_steady_full_keep（右端裸 ev_b(s) 形态，核行    *)
(*         归一化 Σ ev_t(s,·) == 1 在全保留时成立并吸收）。                  *)
(* 件 1c  eviction_steady_deviation_zero   ：定理 6.1 偏差恒为零（Id 形态   *)
(*         + le 形态并列），供论文"定理 6.1 右端恒为零"直接引用。           *)
(* 件 2   eviction_partition_increment     ：保留集扩张的精确增量恒等式     *)
(*         （L29485 单调 ≤ 的等式升级）；并列交付全配分差恒等式             *)
(*         eviction_partition_le_full_exact（L29526 的等式升级）。           *)
(*                                                                           *)
(* 分界注记（对照根 Real-KV 区）：本件零破缺严格依赖 detailed_balance      *)
(* 前提；对称核世界（无 detailed_balance）破缺非零，两层不可互相无条件化。  *)
(* 纯构造性：Set 层语句、Type 版 Or/Not/Id/le/lt，零经典逻辑。              *)
(* ========================================================================= *)


Section UpEvictId.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* ---- 与根 AttentionGibbsBridge 同款世界（变量名/前提形态对齐） ---- *)

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo : R := sum_over_S boltzmann_factor.

Variable Z_thermo_pos : lt zero Z_thermo.

Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_dist_attn s) (transition s s'))
       (mult (boltzmann_dist_attn s') (transition s' s)).

Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition cwe_evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition cwe_evicted_partition : R :=
  sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero cwe_evicted_partition.

Definition cwe_evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos cwe_evicted_partition evicted_partition_pos) (boltzmann_factor s)
  else zero.

Definition cwe_db_breaking (s s' : S) : R :=
  abs (minus (mult (cwe_evicted_boltzmann s) (cwe_evicted_transition s s'))
             (mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s))).

(* 保留集参数化的条件配分函数（单调性/增量比较所需，同根 L29446） *)
Definition cwe_evicted_partition_of (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then boltzmann_factor s else zero).

(* ---- 局部代数辅助（根内无现成 Set 层 minus_zero_r / opp_zero） ---- *)

Lemma opp_zero_u : Id (opp zero) zero.
Proof.
  apply (plus_inv_unique zero (opp zero) zero (plus_opp zero)).
  exact (plus_zero zero).
Qed.

Lemma minus_zero_r_u : forall a : R, Id (minus a zero) a.
Proof.
  intro a.
  unfold minus.
  apply (id_trans (id_cong (fun x => plus a x) opp_zero_u) (plus_zero a)).
Qed.

(* ---- 因子层详细平衡：detailed_balance 消去 Z_thermo 逆元 ----
   （件 1a 的代数核心：bd(s)·t(s,s') == bd(s')·t(s',s) 两侧乘 Z_thermo
     后由 inv_pos_correct + mult_one 吸收逆元。） *)
Lemma boltzmann_factor_detailed_balance :
  forall s s' : S,
    Id (mult (boltzmann_factor s) (transition s s'))
       (mult (boltzmann_factor s') (transition s' s)).
Proof.
  intros s s'.
  pose proof (detailed_balance s s') as Hdb.
  unfold boltzmann_dist_attn in Hdb.
  pose proof (inv_pos_correct Z_thermo Z_thermo_pos) as HZinv.
  pose proof
    (id_trans
       (mult_assoc Z_thermo
                   (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                   (transition s s'))
       (id_cong (fun x => mult x (transition s s'))
                (id_trans (mult_assoc Z_thermo (inv_pos Z_thermo Z_thermo_pos)
                                        (boltzmann_factor s))
                          (id_trans (id_cong (fun x => mult x (boltzmann_factor s)) HZinv)
                                    (id_trans (mult_comm one (boltzmann_factor s))
                                              (mult_one (boltzmann_factor s))))))) as HZl.
  pose proof
    (id_trans
       (mult_assoc Z_thermo
                   (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s'))
                   (transition s' s))
       (id_cong (fun x => mult x (transition s' s))
                (id_trans (mult_assoc Z_thermo (inv_pos Z_thermo Z_thermo_pos)
                                        (boltzmann_factor s'))
                          (id_trans (id_cong (fun x => mult x (boltzmann_factor s')) HZinv)
                                    (id_trans (mult_comm one (boltzmann_factor s'))
                                              (mult_one (boltzmann_factor s'))))))) as HZr.
  exact (id_trans (id_sym HZl) (id_trans (id_cong (fun x => mult Z_thermo x) Hdb) HZr)).
Qed.

(* ---- 掩码核逐点详细平衡（件 1a/1b 共用核心）：任一端逐出则两积同为
   零；双保留时由因子层详细平衡 + cwe_evicted_partition 逆元缩放。4 分支全
   构造性（对照根 L29573 全保留特例的同款分支工艺）。 *)
Lemma evicted_db_products :
  forall s s' : S,
    Id (mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s))
       (mult (cwe_evicted_boltzmann s) (cwe_evicted_transition s s')).
Proof.
  intros s s'.
  unfold cwe_evicted_boltzmann, cwe_evicted_transition.
  destruct (keep_dec s) as [Hs | Hs]; destruct (keep_dec s') as [Hs' | Hs'].
  - (* 双保留：inv_ev·f(s')·t(s',s) == inv_ev·f(s)·t(s,s') *)
    pose proof (id_sym (boltzmann_factor_detailed_balance s s')) as Hf.
    apply (id_trans (id_sym (mult_assoc
                               (inv_pos cwe_evicted_partition evicted_partition_pos)
                               (boltzmann_factor s') (transition s' s)))).
    apply (id_trans (id_cong (fun x => mult (inv_pos cwe_evicted_partition evicted_partition_pos) x)
                             Hf)).
    apply (mult_assoc (inv_pos cwe_evicted_partition evicted_partition_pos)
                      (boltzmann_factor s) (transition s s')).
  - (* s 保留、s' 逐出：两积同为零 *)
    exact (id_trans (mult_zero zero)
                    (id_sym (mult_zero (mult (inv_pos cwe_evicted_partition evicted_partition_pos)
                                             (boltzmann_factor s))))).
  - (* s 逐出、s' 保留：两积同为零 *)
    exact (id_trans (mult_zero (mult (inv_pos cwe_evicted_partition evicted_partition_pos)
                                     (boltzmann_factor s')))
                    (id_sym (mult_zero zero))).
  - (* 双逐出 *)
    reflexivity.
Qed.

(* ================= 件 1a：破缺恒为零（涨落-耗散假设整体多余） ============ *)

Theorem eviction_db_breaking_zero :
  forall s s' : S, Id (cwe_db_breaking s s') zero.
Proof.
  intros s s'.
  unfold cwe_db_breaking.
  apply (id_trans (id_cong abs
    (minus_self_zero (mult (cwe_evicted_boltzmann s) (cwe_evicted_transition s s'))
                     (mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s))
                     (id_sym (evicted_db_products s s'))))).
  exact abs_zero.
Qed.

(* ================= 件 1b：截断核稳态方程（精确恒等式） ====================
   形态 = 扫描报告 A1 草案逐字：Σ_{s'} ev_b(s')·ev_t(s',s)
   == ev_b(s)·Σ_{s'} ev_t(s,s')（保留因子显式出现在右端——掩码核行和
   Σ ev_t(s,·) 一般 < 1，等于 1 仅在全保留时成立，见下方特例）。 *)

Theorem evicted_boltzmann_steady_exact :
  forall s : S,
    Id (sum_over_S (fun s' => mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s)))
       (mult (cwe_evicted_boltzmann s) (sum_over_S (fun s' => cwe_evicted_transition s s'))).
Proof.
  intro s.
  apply (id_trans (sum_over_S_ext
                    (fun s' => mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s))
                    (fun s' => mult (cwe_evicted_boltzmann s) (cwe_evicted_transition s s'))
                    (fun s' => id_sym (evicted_db_products s' s)))).
  apply (sum_over_S_linear (cwe_evicted_boltzmann s) (fun s' => cwe_evicted_transition s s')).
Qed.

(* 全保留桥：ev_t 逐点回到 t（对照根 L29506 eviction_transition_full） *)
Lemma eviction_transition_pointwise_full :
  (forall s, keep s) ->
  forall s s' : S, Id (cwe_evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold cwe_evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + reflexivity.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* 全保留时掩码核行归一化：Σ ev_t(s,·) == 1（transition_normalization 吸收） *)
Lemma evicted_transition_row_sum_one :
  (forall s, keep s) ->
  forall s : S, Id (sum_over_S (fun s' => cwe_evicted_transition s s')) one.
Proof.
  intros Hkall s.
  apply (id_trans (sum_over_S_ext (fun s' => cwe_evicted_transition s s')
                                  (fun s' => transition s s')
                                  (fun s' => eviction_transition_pointwise_full Hkall s s'))).
  apply (transition_normalization s).
Qed.

(* 特例（右端裸 ev_b(s) 形态）：全保留时截断核稳态方程即完整稳态方程 *)
Corollary evicted_boltzmann_steady_full_keep :
  (forall s, keep s) ->
  forall s : S,
    Id (sum_over_S (fun s' => mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s)))
       (cwe_evicted_boltzmann s).
Proof.
  intros Hkall s.
  apply (id_trans (evicted_boltzmann_steady_exact s)).
  apply (id_trans (id_cong (fun x => mult (cwe_evicted_boltzmann s) x)
                           (evicted_transition_row_sum_one Hkall s))).
  apply (mult_one (cwe_evicted_boltzmann s)).
Qed.

(* ================= 件 1c：定理 6.1 偏差恒为零（1b 一步推论） =============
   根 L29626 的界 |稳态差| ≤ Σ cwe_db_breaking 之右端逐项为零，故稳态差
   恒为零——"逐出代价在支撑收缩而非平稳性破坏"的精确形态。 *)

Theorem eviction_steady_deviation_zero :
  forall s : S,
    Id (abs (minus (sum_over_S (fun s' => mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s)))
                   (mult (cwe_evicted_boltzmann s) (sum_over_S (fun s' => cwe_evicted_transition s s')))))
       zero.
Proof.
  intro s.
  apply (id_trans (id_cong abs
    (minus_self_zero
       (sum_over_S (fun s' => mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s)))
       (mult (cwe_evicted_boltzmann s) (sum_over_S (fun s' => cwe_evicted_transition s s')))
       (evicted_boltzmann_steady_exact s)))).
  exact abs_zero.
Qed.

Corollary eviction_steady_deviation_le_zero :
  forall s : S,
    le (abs (minus (sum_over_S (fun s' => mult (cwe_evicted_boltzmann s') (cwe_evicted_transition s' s)))
                   (mult (cwe_evicted_boltzmann s) (sum_over_S (fun s' => cwe_evicted_transition s s')))))
       zero.
Proof.
  intro s.
  apply (le_id_l _ zero zero).
  - apply (eviction_steady_deviation_zero s).
  - apply le_refl.
Qed.

(* ================= 件 2：保留集扩张的精确增量恒等式 ======================
   L29485 单调 ≤ 的等式升级：k1 ⊆ k2 时新增保留质量的精确值 =
   "新入选状态（kd2 真、kd1 假）的 Boltzmann 质量之和"。 *)

Lemma partition_increment_pointwise :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    Id (minus (if kd2 s then boltzmann_factor s else zero)
              (if kd1 s then boltzmann_factor s else zero))
       (if kd2 s then (if kd1 s then zero else boltzmann_factor s) else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | H1]; destruct (kd2 s) as [H2 | H2].
  - (* kd1 s ∧ kd2 s：f − f = 0 *)
    apply (minus_self_zero (boltzmann_factor s) (boltzmann_factor s)).
    apply id_refl.
  - (* kd1 s ∧ ¬kd2 s：与 Hsub 矛盾 *)
    exact (match H2 (Hsub s H1) with end).
  - (* ¬kd1 s ∧ kd2 s：f − 0 = f（新入选态贡献全额质量） *)
    apply (minus_zero_r_u (boltzmann_factor s)).
  - (* ¬kd1 s ∧ ¬kd2 s：0 − 0 = 0 *)
    apply (minus_self_zero zero zero).
    apply id_refl.
Qed.

Theorem eviction_partition_increment :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    Id (minus (cwe_evicted_partition_of k2 kd2) (cwe_evicted_partition_of k1 kd1))
       (sum_over_S (fun s => if kd2 s then (if kd1 s then zero else boltzmann_factor s)
                            else zero)).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold cwe_evicted_partition_of.
  apply (id_trans (id_sym (sum_over_S_minus
                            (fun s => if kd2 s then boltzmann_factor s else zero)
                            (fun s => if kd1 s then boltzmann_factor s else zero)))).
  apply (sum_over_S_ext
           (fun s => minus (if kd2 s then boltzmann_factor s else zero)
                           (if kd1 s then boltzmann_factor s else zero))
           (fun s => if kd2 s then (if kd1 s then zero else boltzmann_factor s) else zero)).
  intro s.
  apply (partition_increment_pointwise k1 k2 Hsub kd1 kd2 s).
Qed.

(* 并列：全配分差恒等式（L29526 ≤ 的等式升级）——
   逐出质量损失 Z_thermo − cwe_evicted_partition(k) = 被逐出态质量之和。 *)
Corollary eviction_partition_le_full_exact :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    Id (minus Z_thermo (cwe_evicted_partition_of k kd))
       (sum_over_S (fun s => if kd s then zero else boltzmann_factor s)).
Proof.
  intros k kd.
  unfold Z_thermo, cwe_evicted_partition_of.
  apply (id_trans (id_sym (sum_over_S_minus boltzmann_factor
                            (fun s => if kd s then boltzmann_factor s else zero)))).
  apply (sum_over_S_ext
           (fun s => minus (boltzmann_factor s) (if kd s then boltzmann_factor s else zero))
           (fun s => if kd s then zero else boltzmann_factor s)).
  intro s.
  destruct (kd s) as [Hk | Hk].
  - apply (minus_self_zero (boltzmann_factor s) (boltzmann_factor s)).
    apply id_refl.
  - apply (minus_zero_r_u (boltzmann_factor s)).
Qed.

End UpEvictId.

(* ---- 提取探针（可提取性验证；G3 关卡对象） ---- *)
Extraction "up_evict_ww_probe.ml" evicted_db_products
  eviction_db_breaking_zero evicted_boltzmann_steady_exact
  evicted_boltzmann_steady_full_keep eviction_steady_deviation_zero
  eviction_partition_increment eviction_partition_le_full_exact.
End EvictId.

(* ---------- UpDebtGibbsT ---------- *)
Module DebtGibbsT.

(* 作用域重指向：同 EvictId——EnhancedMod req 形态代数引理名让位 219 Id 形态。 *)
Local Notation plus_assoc := plus_assoc (only parsing).
Local Notation plus_comm := plus_comm (only parsing).
Local Notation plus_zero := plus_zero (only parsing).
Local Notation plus_opp := plus_opp (only parsing).
Local Notation mult_assoc := mult_assoc (only parsing).
Local Notation mult_comm := mult_comm (only parsing).
Local Notation mult_one := mult_one (only parsing).
Local Notation mult_zero := mult_zero (only parsing).

(* ============================================================ *)
(* UpDebtGibbsT.v —— 债务清理打包席（件 1，方案三 c）            *)
(*   attention_is_gibbs_temp 的 Real 层复刻：任意温度下          *)
(*   softmax == Boltzmann。                                      *)
(*                                                              *)
(*   模板 = 根内单位温度版 real_attention_is_gibbs               *)
(*   （CW214KL_scan L43231）逐字平移：                           *)
(*     温度相等前提 real_eq (inv T) (inv D)                      *)
(*     + energy == −logits + 配分相等                            *)
(*     ⟹ 逐点 real_eq (cwe_real_softmax_temp s) (real_boltzmann_dist_attn s). *)
(*                                                              *)
(*   Real 层原本无温度化 softmax/配分定义，此处先建：            *)
(*     cwe_real_partition_function_temp := Σ e^{z/T}，               *)
(*     cwe_real_softmax_temp s := e^{z_s/T}·inv(Z_T)，               *)
(*   并配套正性/归一化小引理。证明核：real_inv 代数 +            *)
(*   cauchy_real_exp_wd + real_inv_pos_ext + real_mult_comm ——   *)
(*   单位温度版每一步都有对应。                                  *)
(*                                                              *)
(*   世界选择跟随根内 real_attention_is_gibbs（CW214KL_scan；    *)
(*   CW_ConstructiveWorld_219.vo 与本地 9.0/9.1 平台 vo 版本号   *)
(*   不兼容，见交付报告）。                                      *)
(*                                                              *)
(*   纪律：纯构造性、零承认；语句全 Set 层（real_lt/real_eq/     *)
(*   sigT/库内 And）；全部 Qed 收口。                            *)
(* ============================================================ *)


Section RealAttnGibbsTemp.

(* 抽象状态空间（Real 层 Section 自声明，同 RealAttnMain 先例） *)
Variable S : Type.

(* 诚实接口：抽象 S 上的求和（Real 层可实例化；零公理） *)
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s => real_mult a (f s))) (real_mult a (real_sum_over_S f)).

(* 温度（推理侧 T 与热力学侧 D）、能量、logits（Real 层） *)
Variable T : Real.
Variable T_pos : real_lt real_zero T.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.
Variable z_logits : S -> Real.

(* ---- 基础助手：real_exp_neg 的 real_eq 外延 ---- *)
(*（cauchy_real_exp_wd 的 real_exp_neg 形态；real_exp_neg x       *)
(*  定义性 = cauchy_real_exp (−x)）                              *)
Lemma real_exp_neg_wd : forall a b : Real,
  real_eq a b -> real_eq (real_exp_neg a) (real_exp_neg b).
Proof.
  intros a b H. unfold real_exp_neg.
  apply cauchy_real_exp_wd.
  apply (RealSetoid.real_eq_opp_compat a b H).
Qed.

(* ---- 温度化配分函数（Real 层）：Z_T := Σ_s e^{z_s/T} ---- *)
Definition cwe_real_partition_function_temp : Real :=
  real_sum_over_S (fun s => real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s))).

Lemma cwe_real_partition_function_temp_pos : real_lt real_zero cwe_real_partition_function_temp.
Proof.
  unfold cwe_real_partition_function_temp, real_exp_pos_fn.
  apply real_sum_pos_preserved.
  intro s. apply real_exp_neg_pos.
Qed.

(* ---- 温度化 softmax（Real 层）：e^{z_s/T}·inv(Z_T) ---- *)
Definition cwe_real_softmax_temp (s : S) : Real :=
  real_mult (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
            (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos).

(* 配套正性：exp 恒正 × inv 正（real_mult_pos_compat） *)
Theorem real_softmax_temp_pos : forall s : S, real_lt real_zero (cwe_real_softmax_temp s).
Proof.
  intro s. unfold cwe_real_softmax_temp, real_exp_pos_fn.
  apply real_mult_pos_compat.
  - apply real_exp_neg_pos.
  - apply real_inv_pos_pos.
Qed.

(* 配套归一化：Σ_s cwe_softmax_temp(s) == 1
   链：逐 s 乘子交换（sum_ext + real_mult_comm）→ 标量线性提取
   （sum_linear）→ inv(Z_T)·Z_T == 1（real_inv_pos_correct）。 *)
Theorem real_softmax_temp_normalized :
  real_eq (real_sum_over_S (fun s => cwe_real_softmax_temp s)) real_one.
Proof.
  unfold cwe_real_softmax_temp.
  apply (real_eq_trans
          (real_sum_over_S (fun s => real_mult
                             (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                             (real_inv_pos cwe_real_partition_function_temp
                                           cwe_real_partition_function_temp_pos)))
          (real_mult (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos)
                     (real_sum_over_S (fun s =>
                       real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
          real_one).
  - (* 1. 乘子交换后线性提取 *)
    apply (real_eq_trans
            (real_sum_over_S (fun s => real_mult
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))
                               (real_inv_pos cwe_real_partition_function_temp
                                             cwe_real_partition_function_temp_pos)))
            (real_sum_over_S (fun s => real_mult
                               (real_inv_pos cwe_real_partition_function_temp
                                             cwe_real_partition_function_temp_pos)
                               (real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            _).
    + apply real_sum_over_S_ext.
      intro s. apply real_mult_comm.
    + apply real_sum_over_S_linear.
  - (* 2. inv(Z_T)·Z_T == 1 *)
    apply (real_eq_trans
            (real_mult (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos)
                       (real_sum_over_S (fun s =>
                         real_exp_pos_fn (real_mult (real_inv_pos T T_pos) (z_logits s)))))
            (real_mult (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos)
                       cwe_real_partition_function_temp)
            real_one).
    + apply real_eq_refl.
    + apply (real_eq_trans
              (real_mult (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos)
                         cwe_real_partition_function_temp)
              (real_mult cwe_real_partition_function_temp
                         (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos))
              real_one).
      * apply real_mult_comm.
      * apply real_inv_pos_correct.
Qed.

(* ---- Boltzmann 侧（同单位温度版结构） ---- *)
(* Boltzmann 因子（Real 层）：e^{−e(s)/D} *)
Definition cwe_real_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

(* 热力学配分（Real 层）：Σ_s boltzmann_factor *)
Definition cwe_real_Z_thermo : Real := real_sum_over_S cwe_real_boltzmann_factor.

Variable real_Z_thermo_pos : real_lt real_zero cwe_real_Z_thermo.

(* Boltzmann 分布（Real 层）：inv(Z_thermo)·factor *)
Definition cwe_real_boltzmann_dist_attn (s : S) : Real :=
  real_mult (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos) (cwe_real_boltzmann_factor s).

(* ---- 旗舰（件 1）：任意温度下 softmax == Boltzmann ----
   前提：① 1/T == 1/D（温度统一，real_inv_pos 按位相等）
         ② energy == −logits（逐 s）
         ③ Z_thermo == Z_T（配分相等）
   结论：逐 s：cwe_real_softmax_temp s == cwe_real_boltzmann_dist_attn s。
   证明核（单位温度版每步对应）：
     因子桥（real_opp_mult + 温度统一 + energy 替换 + exp 外延）
     → 逆元统一（HZ + real_inv_pos_ext）
     → 组装（mult 交换 + mult_compat 四槽按位）。 *)
Theorem real_attention_is_gibbs_temp :
  (real_eq (real_inv_pos T T_pos) (real_inv_pos D D_pos)) ->
  (forall s : S, real_eq (energy s) (real_opp (z_logits s))) ->
  real_eq cwe_real_Z_thermo cwe_real_partition_function_temp ->
  forall s : S, real_eq (cwe_real_softmax_temp s) (cwe_real_boltzmann_dist_attn s).
Proof.
  intros HDT Henergy HZ s.
  unfold cwe_real_softmax_temp, cwe_real_boltzmann_dist_attn, cwe_real_boltzmann_factor, real_exp_pos_fn.
  (* 1. 因子桥：e^{-(-z(s)/T)} == e^{-e(s)/D} *)
  assert (Hf : real_eq (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))).
  {
    apply real_exp_neg_wd.
    apply (real_eq_trans _ (real_mult (real_inv_pos D D_pos) (real_opp (z_logits s))) _).
    - apply (real_eq_trans _ (real_mult (real_inv_pos T T_pos) (real_opp (z_logits s))) _).
      + (* −(z/T) == (1/T)·(−z)（real_opp_mult） *)
        apply real_opp_mult.
      + (* (1/T)·(−z) == (1/D)·(−z)（温度统一 HDT） *)
        apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos T T_pos) (real_inv_pos D D_pos)
                (real_opp (z_logits s)) (real_opp (z_logits s))
                HDT (real_eq_refl _)).
    - (* (1/D)·(−z) == (1/D)·e（energy == −logits，对称） *)
      apply (RealSetoid.real_eq_mult_compat_adapt
              (real_inv_pos D D_pos) (real_inv_pos D D_pos)
              (real_opp (z_logits s)) (energy s)
              (real_eq_refl _) (real_eq_sym _ _ (Henergy s))).
  }
  (* 2. 逆元统一：inv(Z_thermo) == inv(Z_T)（HZ + real_inv_pos_ext） *)
  assert (Hie : real_eq (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos)
                        (real_inv_pos cwe_real_partition_function_temp
                                      cwe_real_partition_function_temp_pos)).
  { apply (real_inv_pos_ext cwe_real_Z_thermo cwe_real_partition_function_temp
                            real_Z_thermo_pos cwe_real_partition_function_temp_pos).
    exact HZ. }
  (* 3. 组装（镜像单位温度版第 3 步） *)
  apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                    (real_inv_pos cwe_real_partition_function_temp
                                                  cwe_real_partition_function_temp_pos)) _).
  - apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                                      (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos)) _).
    + apply (RealSetoid.real_eq_mult_compat_adapt
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
              (real_inv_pos cwe_real_partition_function_temp cwe_real_partition_function_temp_pos)
              (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos)
              (real_eq_refl _) (real_eq_sym _ _ Hie)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos)
                                        (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))) _).
      * apply real_mult_comm.
      * apply (RealSetoid.real_eq_mult_compat_adapt
                (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos)
                (real_inv_pos cwe_real_Z_thermo real_Z_thermo_pos)
                (real_exp_neg (real_opp (real_mult (real_inv_pos T T_pos) (z_logits s))))
                (real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)))
                (real_eq_refl _) Hf).
Qed.

End RealAttnGibbsTemp.
End DebtGibbsT.

(* ---------- UpDPOLip ---------- *)
Module DPOLip.
(* ============================================================ *)
(* UpDPOLip.v —— A4/B5 升级：DPO softplus-Lipschitz 敏感性界     *)
(* 日期：2026-09-07。源：热点扫描 A4/B5（分析-219平凡定理热点扫描） *)
(* 件 1 real_softplus 定义 + 恒等桥 + 单调性                     *)
(* 件 2 real_softplus_diff_le（序前提单侧核，Lipschitz 数学核）   *)
(*      + real_softplus_lipschitz（Or 序前提 abs/metric 推论）   *)
(* 件 3 real_dpo_pair_loss_sensitivity（DPO 损失敏感性装配）      *)
(* 纪律：纯构造性 / Set 层 / 零 Axiom / 零 Admitted / 零经典。    *)
(* 诚实边界：库内 real_le := Or real_lt real_eq（强编码），abs 形  *)
(*   态无条件全称版需序二分（LPO 等价，构造性不可达）；故 abs 版  *)
(*   以 Or (real_le x y) (real_le y x) 为显式 Set 层前提          *)
(*   （E-STAGING-EntGain-5 先例工艺，语句不降级）。              *)
(* ============================================================ *)


(* ============================================================ *)
(* 件 1：real_softplus 定义、恒等桥、单调性                      *)
(* ============================================================ *)

(* softplus x := log(1 + e^{−x})（DPO logit 损失的 softplus 形态；
   正性证书复用根内 real_sigmoid_denom_pos：1 + e^{−x} > 0）。 *)
Definition real_softplus (x : Real) : Real :=
  real_log (real_plus real_one (real_exp_neg x)) (real_sigmoid_denom_pos x).

(* 恒等桥：real_softplus x == real_dpo_logit x == −log σ(x)。 *)
Lemma real_softplus_eq_dpo_logit : forall x : Real,
  real_eq (real_softplus x) (real_dpo_logit x).
Proof. intro x. apply real_eq_sym. exact (real_softplus_sigmoid_eq x). Qed.

(* 单调性（递减）：x ≤ y ⟹ softplus y ≤ softplus x
   （exp_neg 递减给 1+e^{−y} ≤ 1+e^{−x}；log 保序收口）。 *)
Lemma real_softplus_mono : forall x y : Real, real_le x y ->
  real_le (real_softplus y) (real_softplus x).
Proof.
  intros x y Hxy.
  apply (real_log_le_mono (real_plus real_one (real_exp_neg y))
                          (real_plus real_one (real_exp_neg x))
                          (real_sigmoid_denom_pos y)
                          (real_sigmoid_denom_pos x)).
  exact (real_le_plus_compat real_one real_one
                             (real_exp_neg y) (real_exp_neg x)
                             (real_le_refl real_one)
                             (real_exp_neg_le_decr x y Hxy)).
Qed.

(* u ≤ 0 ⟹ 1 ≤ e^{−u}（e^0 == 1 换形 + exp_neg 递减）。 *)
Lemma real_one_le_exp_neg_of_le_zero : forall u : Real, real_le u real_zero ->
  real_le real_one (real_exp_neg u).
Proof.
  intros u Hu.
  apply (real_le_trans real_one (real_exp_neg real_zero) (real_exp_neg u)).
  - apply real_eq_le_bridge.
    apply real_eq_sym. exact real_exp_neg_zero.
  - exact (real_exp_neg_le_decr u real_zero Hu).
Qed.

(* b ≤ a ⟹ b − a ≤ 0（减法非正；加法保序 + a + (−a) == 0）。 *)
Lemma real_diff_le_zero : forall a b : Real, real_le b a ->
  real_le (real_plus b (real_opp a)) real_zero.
Proof.
  intros a b Hba.
  apply (real_le_trans (real_plus b (real_opp a))
                       (real_plus a (real_opp a)) real_zero).
  - exact (real_le_plus_compat b a (real_opp a) (real_opp a)
                                  Hba (real_le_refl (real_opp a))).
  - apply real_eq_le_bridge. exact (real_plus_opp a).
Qed.

(* 代数：e^{−b} == e^{−a}·e^{−(b−a)}（参数换形 + exp 加法性）。 *)
Lemma cwe_real_exp_neg_split : forall a b : Real,
  real_eq (real_exp_neg b)
          (real_mult (real_exp_neg a)
                     (real_exp_neg (real_plus b (real_opp a)))).
Proof.
  intros a b.
  apply (real_eq_trans (real_exp_neg b)
                       (real_exp_neg (real_plus a (real_plus b (real_opp a)))) _).
  - unfold real_exp_neg. apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_opp_compat b (real_plus a (real_plus b (real_opp a)))).
    apply real_eq_sym.
    (* a + (b − a) == b：assoc → comm → assoc⁻¹ → opp 消去 → 右零 *)
    apply (real_eq_trans (real_plus a (real_plus b (real_opp a)))
                         (real_plus (real_plus a b) (real_opp a)) b).
    + exact (real_plus_assoc a b (real_opp a)).
    + apply (real_eq_trans (real_plus (real_plus a b) (real_opp a))
                           (real_plus (real_plus b a) (real_opp a)) b).
      * apply (RealSetoid.real_eq_plus_compat (real_plus a b) (real_opp a)
                                              (real_plus b a) (real_opp a)).
        -- exact (real_plus_comm a b).
        -- apply real_eq_refl.
      * apply (real_eq_trans (real_plus (real_plus b a) (real_opp a))
                             (real_plus b (real_plus a (real_opp a))) b).
        -- apply real_eq_sym.
           exact (real_plus_assoc b a (real_opp a)).
        -- apply (real_eq_trans (real_plus b (real_plus a (real_opp a)))
                                (real_plus b real_zero) b).
           ++ apply (RealSetoid.real_eq_plus_compat b (real_plus a (real_opp a))
                                                    b real_zero).
              ** apply real_eq_refl.
              ** exact (real_plus_opp a).
           ++ exact (real_plus_zero b).
  - exact (real_exp_neg_plus a (real_plus b (real_opp a))).
Qed.

(* ============================================================ *)
(* 件 2：序前提单侧核（Lipschitz 数学核）                        *)
(*   b ≤ a ⟹ softplus b − softplus a ≤ a − b                     *)
(* 数学核：1+e^{−b} ≤ e^{a−b} + e^{−b} == (1+e^{−a})·e^{a−b}     *)
(*   （e^{a−b} ≥ 1 由 b ≤ a），两侧取 log + log 加法性收口。      *)
(* ============================================================ *)
Lemma real_softplus_diff_le : forall a b : Real, real_le b a ->
  real_le (real_plus (real_softplus b) (real_opp (real_softplus a)))
          (real_plus a (real_opp b)).
Proof.
  intros a b Hba.
  set (u := real_plus b (real_opp a)).
  set (E := real_exp_neg u).
  set (A := real_plus real_one (real_exp_neg a)).
  set (B := real_plus real_one (real_exp_neg b)).
  (* 步 1：E = e^{a−b} ≥ 1 *)
  assert (Hu0 : real_le u real_zero) by exact (real_diff_le_zero a b Hba).
  assert (HE1 : real_le real_one E) by exact (real_one_le_exp_neg_of_le_zero u Hu0).
  (* 步 2：恒等式 A·E == E + e^{−b} *)
  assert (HQ : real_eq (real_mult A E) (real_plus E (real_exp_neg b))).
  { apply (real_eq_trans (real_mult A E)
           (real_plus (real_mult E real_one) (real_mult E (real_exp_neg a))) _).
    - apply (real_eq_trans (real_mult A E)
              (real_mult E (real_plus real_one (real_exp_neg a))) _).
      + exact (real_mult_comm A E).
      + exact (real_distrib E real_one (real_exp_neg a)).
    - apply (RealSetoid.real_eq_plus_compat (real_mult E real_one)
                                            (real_mult E (real_exp_neg a))
                                            E (real_exp_neg b)).
      + exact (real_mult_one E).
      + (* E·e^{−a} == e^{−b}：cwe_real_exp_neg_split + 乘法交换 *)
        apply real_eq_sym.
        apply (real_eq_trans (real_exp_neg b)
                             (real_mult (real_exp_neg a) E) _).
        * exact (cwe_real_exp_neg_split a b).
        * exact (real_mult_comm (real_exp_neg a) E).
  }
  (* 步 3：B ≤ A·E（1 ≤ E 加法保序 + 恒等式换形） *)
  assert (HB : real_le B (real_mult A E)).
  { apply (real_le_trans B (real_plus E (real_exp_neg b)) (real_mult A E)).
    - exact (real_le_plus_compat real_one E (real_exp_neg b) (real_exp_neg b)
                                  HE1 (real_le_refl (real_exp_neg b))).
    - apply real_eq_le_bridge. apply real_eq_sym. exact HQ.
  }
  (* 步 4：log 收口：softplus b ≤ softplus a + (a − b) *)
  assert (Hlog : real_le (real_softplus b)
                         (real_plus (real_softplus a) (real_plus a (real_opp b)))).
  { apply (real_le_trans (real_softplus b)
             (real_log (real_mult A E)
                       (real_mult_positive A E (real_sigmoid_denom_pos a)
                                           (real_exp_neg_pos u))) _).
    - apply (real_log_le_mono B (real_mult A E) (real_sigmoid_denom_pos b)
              (real_mult_positive A E (real_sigmoid_denom_pos a)
                                      (real_exp_neg_pos u)) HB).
    - apply real_eq_le_bridge.
      apply (real_eq_trans (real_log (real_mult A E)
                (real_mult_positive A E (real_sigmoid_denom_pos a)
                                        (real_exp_neg_pos u)))
        (real_plus (real_log A (real_sigmoid_denom_pos a))
                   (real_log E (real_exp_neg_pos u))) _).
      + exact (real_log_mult A E (real_sigmoid_denom_pos a) (real_exp_neg_pos u)).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_log A (real_sigmoid_denom_pos a))
                 (real_log E (real_exp_neg_pos u))
                 (real_softplus a) (real_plus a (real_opp b))).
        * apply real_eq_refl.
        * (* log E == −(b−a) == a − b：log 左逆 + opp 代数 *)
          apply (real_eq_trans (real_log E (real_exp_neg_pos u))
                               (real_opp u) _).
          -- exact (log_inv_exp_neg_thm (real_opp u) (real_exp_neg_pos u)).
          -- apply (real_eq_trans (real_opp u)
                     (real_plus (real_opp b) (real_opp (real_opp a))) _).
             ++ exact (real_opp_plus b (real_opp a)).
             ++ apply (real_eq_trans (real_plus (real_opp b) (real_opp (real_opp a)))
                                     (real_plus (real_opp b) a) _).
                ** apply (RealSetoid.real_eq_plus_compat (real_opp b)
                            (real_opp (real_opp a)) (real_opp b) a).
                   --- apply real_eq_refl.
                   --- exact (real_opp_opp a).
                ** exact (real_plus_comm (real_opp b) a).
  }
  (* 步 5：移项：softplus b − softplus a ≤ a − b *)
  apply (real_le_trans (real_plus (real_softplus b) (real_opp (real_softplus a)))
                       (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                  (real_opp (real_softplus a))) _).
  - exact (real_le_plus_compat (real_softplus b)
                               (real_plus (real_softplus a) (real_plus a (real_opp b)))
                               (real_opp (real_softplus a)) (real_opp (real_softplus a))
                               Hlog (real_le_refl (real_opp (real_softplus a)))).
  - apply real_eq_le_bridge.
    apply (real_eq_trans (real_plus (real_plus (real_softplus a) (real_plus a (real_opp b)))
                                    (real_opp (real_softplus a)))
                         (real_plus (real_softplus a)
                                    (real_plus (real_plus a (real_opp b))
                                               (real_opp (real_softplus a)))) _).
    + apply real_eq_sym.
      exact (real_plus_assoc (real_softplus a) (real_plus a (real_opp b))
                             (real_opp (real_softplus a))).
    + apply (real_eq_trans (real_plus (real_softplus a)
                              (real_plus (real_plus a (real_opp b))
                                         (real_opp (real_softplus a))))
                           (real_plus (real_softplus a)
                              (real_plus (real_opp (real_softplus a))
                                         (real_plus a (real_opp b)))) _).
      * apply (RealSetoid.real_eq_plus_compat (real_softplus a)
                 (real_plus (real_plus a (real_opp b)) (real_opp (real_softplus a)))
                 (real_softplus a)
                 (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b)))).
        -- apply real_eq_refl.
        -- exact (real_plus_comm (real_plus a (real_opp b))
                                 (real_opp (real_softplus a))).
      * apply (real_eq_trans (real_plus (real_softplus a)
                   (real_plus (real_opp (real_softplus a)) (real_plus a (real_opp b))))
                (real_plus (real_plus (real_softplus a) (real_opp (real_softplus a)))
                           (real_plus a (real_opp b))) _).
        -- exact (real_plus_assoc (real_softplus a) (real_opp (real_softplus a))
                                  (real_plus a (real_opp b))).
        -- apply (real_eq_trans (real_plus (real_plus (real_softplus a)
                                             (real_opp (real_softplus a)))
                                           (real_plus a (real_opp b)))
                                (real_plus real_zero (real_plus a (real_opp b))) _).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_softplus a) (real_opp (real_softplus a)))
                       (real_plus a (real_opp b))
                       real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_opp (real_softplus a)).
              ** apply real_eq_refl.
           ++ apply (real_eq_trans (real_plus real_zero (real_plus a (real_opp b)))
                                   (real_plus (real_plus a (real_opp b)) real_zero) _).
              ** exact (real_plus_comm real_zero (real_plus a (real_opp b))).
              ** exact (real_plus_zero (real_plus a (real_opp b))).
Qed.

(* ============================================================ *)
(* 件 2 收口：abs 消解工具 + Or 序前提 Lipschitz 主推论          *)
(* ============================================================ *)

(* 0 ≤ d ⟹ |d| == d（real_abs_pos_req 的 le 版：Or 两支）。 *)
Lemma real_abs_nonneg_eq : forall d : Real, real_le real_zero d ->
  real_eq (real_abs d) d.
Proof.
  intros d Hd. destruct Hd as [Hlt | Heq].
  - exact (real_abs_pos_req d Hlt).
  - apply (real_eq_trans (real_abs d) real_zero d).
    + apply (real_eq_trans (real_abs d) (real_abs real_zero) real_zero).
      * apply (RealSetoid.real_eq_abs_compat d real_zero (real_eq_sym real_zero d Heq)).
      * exact real_abs_zero_req.
    + exact Heq.
Qed.

(* 减法式的反号形态：u − v == −(v − u)。 *)
Lemma real_minus_opp_form : forall u v : Real,
  real_eq (real_plus u (real_opp v)) (real_opp (real_plus v (real_opp u))).
Proof.
  intros u v.
  apply (real_eq_trans (real_plus u (real_opp v))
                       (real_plus (real_opp v) u) _).
  - exact (real_plus_comm u (real_opp v)).
  - apply (real_eq_trans (real_plus (real_opp v) u)
                         (real_plus (real_opp v) (real_opp (real_opp u))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_opp v) u
                                            (real_opp v) (real_opp (real_opp u))).
      * apply real_eq_refl.
      * apply real_eq_sym. exact (real_opp_opp u).
    + apply real_eq_sym. exact (real_opp_plus v (real_opp u)).
Qed.

(* d == −e 且 0 ≤ e ⟹ |d| == e（abs 经 opp 对称消解）。 *)
Lemma real_abs_opp_form : forall d e : Real,
  real_eq d (real_opp e) -> real_le real_zero e -> real_eq (real_abs d) e.
Proof.
  intros d e Hd He.
  apply (real_eq_trans (real_abs d) (real_abs e) e).
  - apply (real_eq_trans (real_abs d) (real_abs (real_opp e)) (real_abs e)).
    + apply (RealSetoid.real_eq_abs_compat d (real_opp e) Hd).
    + exact (real_abs_opp e).
  - exact (real_abs_nonneg_eq e He).
Qed.

(* 主推论：softplus 的 1-Lipschitz 敏感性界（metric 形态）。
   前提 Or (real_le x y) (real_le y x) 为显式 Set 层序二分
   （构造性实数上不可整体消去，见文件头诚实边界注记）。 *)
Theorem real_softplus_lipschitz : forall x y : Real,
  Or (real_le x y) (real_le y x) ->
  real_le (real_metric (real_softplus x) (real_softplus y))
          (real_metric x y).
Proof.
  intros x y Hor. unfold real_metric.
  destruct Hor as [Hxy | Hyx].
  - (* 分支 1：x ≤ y。|sp x − sp y| == sp x − sp y；|x − y| == y − x。 *)
    assert (Hdec : real_le (real_softplus y) (real_softplus x))
      by exact (real_softplus_mono x y Hxy).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus x) (real_opp (real_softplus y))))
      by exact (real_le_minus_nonneg_aux (real_softplus y) (real_softplus x) Hdec).
    assert (Hd2 : real_le real_zero (real_plus y (real_opp x)))
      by exact (real_le_minus_nonneg_aux x y Hxy).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus x) (real_opp (real_softplus y))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_nonneg_eq (real_plus (real_softplus x) (real_opp (real_softplus y))) Hd1).
    + apply (real_le_trans (real_plus (real_softplus x) (real_opp (real_softplus y)))
                           (real_plus y (real_opp x)) _).
      * exact (real_softplus_diff_le y x Hxy).
      * apply real_eq_le_bridge. apply real_eq_sym.
        exact (real_abs_opp_form (real_plus x (real_opp y))
                                 (real_plus y (real_opp x))
                                 (real_minus_opp_form x y) Hd2).
  - (* 分支 2：y ≤ x。|sp x − sp y| == sp y − sp x（opp 桥）；|x − y| == x − y。 *)
    assert (Hdec : real_le (real_softplus x) (real_softplus y))
      by exact (real_softplus_mono y x Hyx).
    assert (Hd1 : real_le real_zero
                    (real_plus (real_softplus y) (real_opp (real_softplus x))))
      by exact (real_le_minus_nonneg_aux (real_softplus x) (real_softplus y) Hdec).
    assert (Hd2 : real_le real_zero (real_plus x (real_opp y)))
      by exact (real_le_minus_nonneg_aux y x Hyx).
    apply (real_le_trans (real_abs (real_plus (real_softplus x) (real_opp (real_softplus y))))
                         (real_plus (real_softplus y) (real_opp (real_softplus x))) _).
    + apply real_eq_le_bridge.
      exact (real_abs_opp_form (real_plus (real_softplus x) (real_opp (real_softplus y)))
                               (real_plus (real_softplus y) (real_opp (real_softplus x)))
                               (real_minus_opp_form (real_softplus x) (real_softplus y))
                               Hd1).
    + apply (real_le_trans (real_plus (real_softplus y) (real_opp (real_softplus x)))
                           (real_plus x (real_opp y)) _).
      * exact (real_softplus_diff_le x y Hyx).
      * apply real_eq_le_bridge.
        apply real_eq_sym.
        exact (real_abs_nonneg_eq (real_plus x (real_opp y)) Hd2).
Qed.

(* ============================================================ *)
(* 件 3：DPO 损失敏感性装配                                      *)
(*   |L(π; w, l) − L(π*; w, l)| ≤ |β(log_ratio 差分) − (r_w − r_l)| *)
(*   （条件化形态：序二分前提为显式 Set 层 Or）。                *)
(* ============================================================ *)

(* metric 的 eq 兼容。 *)
Lemma real_metric_eq_compat : forall a a' b b' : Real,
  real_eq a a' -> real_eq b b' ->
  real_eq (real_metric a b) (real_metric a' b').
Proof.
  intros a a' b b' Ha Hb. unfold real_metric.
  apply (RealSetoid.real_eq_abs_compat (real_plus a (real_opp b))
                                       (real_plus a' (real_opp b'))).
  apply (RealSetoid.real_eq_plus_compat a (real_opp b) a' (real_opp b') Ha).
  apply (RealSetoid.real_eq_opp_compat b b'). exact Hb.
Qed.

Section UpDpoSensMain.

Variable S : Type.
Variable reward : S -> Real.
Variable beta : Real.
Variable beta_pos : real_lt real_zero beta.
Variable pi_ref : S -> Real.
Variable pi_ref_pos : forall s : S, real_lt real_zero (pi_ref s).
Variable Z_align : Real.
Variable Z_align_pos : real_lt real_zero Z_align.

(* 策略 π 的 DPO logit 差：β·(log_ratio(π, w) − log_ratio(π, l))。 *)
Definition real_dpo_logit_pair (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S) : Real :=
  real_plus (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_w))
            (real_opp (real_mult beta (real_log_ratio S pi_ref pi_ref_pos pi Hpi s_l))).

(* π* 的 DPO logit 差：真实奖励差分 r_w − r_l。 *)
Definition real_dpo_logit_star (s_w s_l : S) : Real :=
  real_plus (reward s_w) (real_opp (reward s_l)).

(* 桥 1：策略 DPO 损失 == softplus(logit 差)（定义性 + softplus 恒等桥）。 *)
Lemma real_dpo_loss_pair_eq_softplus : forall (pi : S -> Real)
  (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
          (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)).
Proof.
  intros pi Hpi s_w s_l.
  apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* 桥 2：π* 处 DPO 损失 == softplus(真实奖励差分)
   （real_dpo_loss_at_pi_star + softplus 恒等桥）。 *)
Lemma real_dpo_loss_star_eq_softplus : forall s_w s_l : S,
  real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
             s_w s_l)
          (real_softplus (real_dpo_logit_star s_w s_l)).
Proof.
  intros s_w s_l.
  apply (real_eq_trans _ (real_dpo_logit (real_dpo_logit_star s_w s_l)) _).
  - exact (real_dpo_loss_at_pi_star S reward beta beta_pos pi_ref pi_ref_pos
                                    Z_align Z_align_pos s_w s_l).
  - apply real_eq_sym. apply real_softplus_eq_dpo_logit.
Qed.

(* 主件：DPO 损失敏感性界（metric 形态，序二分前提显式 Set 层 Or）。
   内容：metric L pi L_star ≤ metric logit pi logit_star
   （策略损失到 pi_star 损失的距离 ≤ logit 差分的距离）。 *)
Theorem real_dpo_pair_loss_sensitivity :
  forall (pi : S -> Real) (Hpi : forall t : S, real_lt real_zero (pi t)) (s_w s_l : S),
  Or (real_le (real_dpo_logit_star s_w s_l) (real_dpo_logit_pair pi Hpi s_w s_l))
      (real_le (real_dpo_logit_pair pi Hpi s_w s_l) (real_dpo_logit_star s_w s_l)) ->
  real_le (real_metric (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                          (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                          (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                          s_w s_l))
          (real_metric (real_dpo_logit_pair pi Hpi s_w s_l)
                       (real_dpo_logit_star s_w s_l)).
Proof.
  intros pi Hpi s_w s_l Hor.
  assert (HL : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos pi Hpi s_w s_l)
                       (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
    by exact (real_dpo_loss_pair_eq_softplus pi Hpi s_w s_l).
  assert (HS : real_eq (real_dpo_loss_pair S beta pi_ref pi_ref_pos
                             (real_pi_star S reward beta beta_pos pi_ref Z_align Z_align_pos)
                             (real_pi_star_pos S reward beta beta_pos pi_ref pi_ref_pos Z_align Z_align_pos)
                             s_w s_l)
                       (real_softplus (real_dpo_logit_star s_w s_l)))
    by exact (real_dpo_loss_star_eq_softplus s_w s_l).
  apply (real_le_trans _ (real_metric (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_softplus (real_dpo_logit_star s_w s_l))) _).
  - apply real_eq_le_bridge.
    exact (real_metric_eq_compat _ _ _ _ HL HS).
  - unfold real_metric.
    destruct Hor as [H | H].
    + (* 分支 1：X* ≤ Xπ ⟹ Lπ ≤ L*；|Lπ − L*| == L* − Lπ ≤ Xπ − X* == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                             (real_softplus (real_dpo_logit_star s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_star s_w s_l)
                                     (real_dpo_logit_pair pi Hpi s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                           (real_softplus (real_dpo_logit_star s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                 (real_opp (real_dpo_logit_star s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_star s_w s_l)
                                           (real_dpo_logit_pair pi Hpi s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_opp_form (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                                 (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                            (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                                 (real_minus_opp_form (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                      (real_softplus (real_dpo_logit_star s_w s_l)))
                                 Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_star s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))))
                             (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_opp (real_dpo_logit_star s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_pair pi Hpi s_w s_l)
                                        (real_dpo_logit_star s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_nonneg_eq (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                                (real_opp (real_dpo_logit_star s_w s_l))) Hd2).
    + (* 分支 2：Xπ ≤ X* ⟹ L* ≤ Lπ；|Lπ − L*| == Lπ − L* ≤ X* − Xπ == |Xπ − X*| *)
      assert (Hdec : real_le (real_softplus (real_dpo_logit_star s_w s_l))
                             (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)))
        by exact (real_softplus_mono (real_dpo_logit_pair pi Hpi s_w s_l)
                                     (real_dpo_logit_star s_w s_l) H).
      assert (Hd1 : real_le real_zero
                      (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                 (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
        by exact (real_le_minus_nonneg_aux (real_softplus (real_dpo_logit_star s_w s_l))
                                           (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l)) Hdec).
      assert (Hd2 : real_le real_zero
                      (real_plus (real_dpo_logit_star s_w s_l)
                                 (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))))
        by exact (real_le_minus_nonneg_aux (real_dpo_logit_pair pi Hpi s_w s_l)
                                           (real_dpo_logit_star s_w s_l) H).
      apply (real_le_trans (real_abs (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                                (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))))
                           (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                      (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) _).
      * apply real_eq_le_bridge.
        exact (real_abs_nonneg_eq (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                             (real_opp (real_softplus (real_dpo_logit_star s_w s_l)))) Hd1).
      * apply (real_le_trans (real_plus (real_softplus (real_dpo_logit_pair pi Hpi s_w s_l))
                                        (real_opp (real_softplus (real_dpo_logit_star s_w s_l))))
                             (real_plus (real_dpo_logit_star s_w s_l)
                                        (real_opp (real_dpo_logit_pair pi Hpi s_w s_l))) _).
        -- exact (real_softplus_diff_le (real_dpo_logit_star s_w s_l)
                                        (real_dpo_logit_pair pi Hpi s_w s_l) H).
        -- apply real_eq_le_bridge.
           apply real_eq_sym.
           exact (real_abs_opp_form (real_plus (real_dpo_logit_pair pi Hpi s_w s_l)
                                               (real_opp (real_dpo_logit_star s_w s_l)))
                                    (real_plus (real_dpo_logit_star s_w s_l)
                                               (real_opp (real_dpo_logit_pair pi Hpi s_w s_l)))
                                    (real_minus_opp_form (real_dpo_logit_pair pi Hpi s_w s_l)
                                                         (real_dpo_logit_star s_w s_l))
                                    Hd2).
Qed.

End UpDpoSensMain.
End DPOLip.

(* ---------- UpDissip ---------- *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import Constitution.
(* ============================================================ *)
(* UpDissip.v —— BEA 2.0 耗散本位界汇经济：券/边/复合律/耗散记账/借据 *)
(*                                                              *)
(* 理论来源：ROUNDTABLE.md 席 3 终稿【BEA 2.0——耗散本位界汇经济】   *)
(*   「不算数、只换界」——券的 eps 槽位 = 严格性量化资源；           *)
(*   每条边 = 带 eps-重参数化的转化定理（入参 eps 仿射映射出参：      *)
(*   eps_out = a·eps_in + b，a > 0）；                              *)
(*   路径合法性 = 仿射复合恒正（沿路径线性可判定）；                 *)
(*   借据 = 未命中签发的缺口义务（可再入）。                         *)
(*                                                              *)
(* 交付六件：                                                    *)
(*   件 1  bond / bond_check   券类型（Set 层 Record）+ 券面校验器    *)
(*   件 2  edge_spec / edge_map / edge_check                       *)
(*                             兑换边：eps 仿射映射 + 斜率正性验证器  *)
(*   件 3  edge_compound_affine 主件：边复合 = eps 仿射复合；        *)
(*         path2_ok 线性可判定路径合法性 + edge_comp_legal          *)
(*   件 4  diss_conservation（币制守恒恒等式）+                     *)
(*         path_dissipation_additive（路径耗散可加）+               *)
(*         path_dissipation_mono（耗散对入参 eps 单调）              *)
(*   件 5  iou_issue 借据签发（查询未命中 → 缺口义务载荷的 inr）      *)
(*         + redeem 借据再入 + redeem_closes（证成 ⟹ 图谱成长闭合）   *)
(*   件 6  vm_compute 自测：3 边图谱 eps/2→eps/4→eps/8 链           *)
(*                                                              *)
(* 层位纪律：语句全 Set 层（QltT/QleT'/Id/sigT/And/Or，判定走        *)
(*   Qle_bool/Qlt_bool/Nat.eqb）；Prop 零出场。消费 UpConstitution   *)
(*   的 Q 层桥（uc_qeq_le 等）。全部 Qed/Defined 闭合。              *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============================================================ *)
(* §1 Q 层微件（消费 UpConstitution 桥；补右加法弱不等式）            *)
(* ============================================================ *)

Lemma ud_le_add_r : forall z w : Q, Qle 0 w -> Qle z (z + w).
Proof.
  intros z w Hw.
  apply (Qle_trans z (z + 0) (z + w)).
  - apply (uc_qeq_le_r z (z + 0) z).
    + ring.
    + apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hw].
Qed.

(* ============================================================ *)
(* §2 件 1：券 bond——界券组合的 Set 层类型                           *)
(*   币制本体：eps 槽位是严格性的量化资源（余量多少 eps）。           *)
(* ============================================================ *)

Record bond : Set := mk_bond {
  bd_id : nat;        (* 命题 id *)
  bd_bound : Q;       (* 界值：不超过哪个上界 *)
  bd_eps : Q;         (* eps 槽位：严格性余量 *)
  bd_src : nat        (* 签发源：哪个度量/格式 *)
}.

(* 券面校验器（Defined 可执行；inr 带拒绝码，对照宪法形态） *)
Inductive bond_reject : Set :=
| br_eps.              (* eps 槽位为负：无严格性余量可让渡 *)

Definition bond_check (bd : bond)
  : Or (QleT' 0 (bd_eps bd)) (And (Id (Qle_bool 0 (bd_eps bd)) false) bond_reject) :=
  match Qle_bool 0 (bd_eps bd) as b
        return Or (Id b true) (And (Id b false) bond_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, br_eps)
  end.

(* ============================================================ *)
(* §3 件 2：兑换边 edge——eps 仿射重参数化的转化定理                   *)
(*   eps_out = a·eps_in + b，a > 0（斜率正 ⟹ 保严格序）。           *)
(* ============================================================ *)

Record edge_spec : Set := mk_edge {
  ed_id : nat;        (* 边 id *)
  ed_src : nat;       (* 源格式（度量索引） *)
  ed_dst : nat;       (* 目标格式 *)
  ed_a : Q;           (* 斜率 a > 0 *)
  ed_b : Q            (* 截距 b *)
}.

Definition edge_map (e : edge_spec) (x : Q) : Q := ed_a e * x + ed_b e.
Definition edge_diss (e : edge_spec) (x : Q) : Q := x - edge_map e x.
Definition edge_ok (e : edge_spec) : bool := Qlt_bool 0 (ed_a e).
Definition edge_bi (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool 0 (ed_b e)).
Definition edge_tame (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool (ed_a e) 1).

(* 边验证器（Defined 可执行；拒绝码形态） *)
Inductive edge_reject : Set :=
| er_slope.             (* 斜率非正：兑换不保严格序 *)

Definition edge_check (e : edge_spec)
  : Or (QltT 0 (ed_a e)) (And (Id (Qlt_bool 0 (ed_a e)) false) edge_reject) :=
  match Qlt_bool 0 (ed_a e) as b
        return Or (Id b true) (And (Id b false) edge_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, er_slope)
  end.

(* 布尔门证书提取：正则边（a>0 ∧ b≥0）的两个 Q 事实 *)
Lemma edge_bi_spec : forall e : edge_spec,
  Id (edge_bi e) true -> And (Qlt 0 (ed_a e)) (Qle 0 (ed_b e)).
Proof.
  intros e H. unfold edge_bi in H.
  destruct (Qlt_bool 0 (ed_a e)) eqn:E1; destruct (Qle_bool 0 (ed_b e)) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  split.
  - apply QltT_to_Qlt. apply RealSetoid.eq_Id. exact E1.
  - apply QleT'_to_Qle. apply RealSetoid.eq_Id. exact E2.
Qed.

(* 温和边（a>0 ∧ a≤1）的两个 Q 事实 *)
Lemma edge_tame_spec : forall e : edge_spec,
  Id (edge_tame e) true -> And (Qlt 0 (ed_a e)) (Qle (ed_a e) 1).
Proof.
  intros e H. unfold edge_tame, edge_ok in H.
  destruct (Qlt_bool 0 (ed_a e)) eqn:E1; destruct (Qle_bool (ed_a e) 1) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  split.
  - apply QltT_to_Qlt. apply RealSetoid.eq_Id. exact E1.
  - apply QleT'_to_Qle. apply RealSetoid.eq_Id. exact E2.
Qed.

(* 边=转化定理的序性质：a>0 ⟹ eps 仿射重参数化严格保序 *)
Lemma edge_strict_mono : forall (e : edge_spec) (x y : Q),
  Qlt 0 (ed_a e) -> Qlt x y -> Qlt (edge_map e x) (edge_map e y).
Proof.
  intros e x y Ha Hxy. unfold edge_map.
  assert (H1 : Qlt (x * ed_a e) (y * ed_a e)).
  { apply (Qmult_lt_compat_r x y (ed_a e) Ha Hxy). }
  assert (H2a : Qlt (ed_a e * x) (y * ed_a e)).
  { apply (uc_qeq_lt_l (x * ed_a e) (ed_a e * x) (y * ed_a e)).
    - ring.
    - exact H1. }
  assert (H2 : Qlt (ed_a e * x) (ed_a e * y)).
  { apply (uc_qeq_lt_r (y * ed_a e) (ed_a e * y) (ed_a e * x)).
    - ring.
    - exact H2a. }
  assert (H3 : Qlt (ed_b e + ed_a e * x) (ed_b e + ed_a e * y)).
  { apply (proj2 (Qplus_lt_r (ed_a e * x) (ed_a e * y) (ed_b e))). exact H2. }
  assert (H4 : Qlt (ed_a e * x + ed_b e) (ed_b e + ed_a e * y)).
  { apply (uc_qeq_lt_l (ed_b e + ed_a e * x)
                       (ed_a e * x + ed_b e)
                       (ed_b e + ed_a e * y)).
    - ring.
    - exact H3. }
  apply (uc_qeq_lt_r (ed_b e + ed_a e * y)
                     (ed_a e * y + ed_b e)
                     (ed_a e * x + ed_b e)).
  - ring.
  - exact H4.
Qed.

(* 正则边保持 eps 槽位严格正（严格性不因兑换湮灭） *)
Lemma edge_map_pos : forall (e : edge_spec) (x : Q),
  QltT 0 x -> Id (edge_bi e) true -> QltT 0 (edge_map e x).
Proof.
  intros e x Hx Hbi.
  pose proof (edge_bi_spec e Hbi) as [Ha Hb].
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (ed_a e * x) (edge_map e x)).
  - apply (Qmult_lt_0_compat (ed_a e) x Ha (QltT_to_Qlt 0 x Hx)).
  - unfold edge_map.
    apply (uc_qeq_le_l (ed_a e * x + 0) (ed_a e * x) (ed_a e * x + ed_b e)).
    + ring.
    + apply Qplus_le_compat; [apply Qle_refl | exact Hb].
Qed.

(* 券沿边兑换：eps 槽位按仿射映射重参数化 *)
Definition bond_exchange (e : edge_spec) (bd : bond) : bond :=
  mk_bond (bd_id bd) (bd_bound bd) (edge_map e (bd_eps bd)) (ed_dst e).

Lemma bond_exchange_eps : forall (e : edge_spec) (bd : bond),
  bd_eps (bond_exchange e bd) == edge_map e (bd_eps bd).
Proof. intros e bd. reflexivity. Qed.

(* 币制守恒（券级实例）：入参 eps = 出参 eps + 耗散 *)
Theorem bond_exchange_conservation : forall (e : edge_spec) (bd : bond),
  bd_eps bd == bd_eps (bond_exchange e bd) + edge_diss e (bd_eps bd).
Proof.
  intros e bd. rewrite bond_exchange_eps.
  unfold edge_diss, edge_map. ring.
Qed.

(* 兑换保严格性：正则边 ⟹ 兑换后 eps 槽位仍严格正 *)
Theorem bond_exchange_pos : forall (e : edge_spec) (bd : bond),
  Id (edge_bi e) true -> QltT 0 (bd_eps bd) ->
  QltT 0 (bd_eps (bond_exchange e bd)).
Proof.
  intros e bd Hbi Hx. unfold bond_exchange.
  apply (edge_map_pos e (bd_eps bd) Hx Hbi).
Qed.

(* ============================================================ *)
(* §4 件 3（主件）：edge_compound_affine——边复合 = eps 仿射复合      *)
(*   复合边斜率 = a2·a1 > 0（恒正线性可判定）；                      *)
(*   路径合法性 = 仿射复合恒正，布尔判定器 path2_ok 线性判定。        *)
(* ============================================================ *)

Definition edge_comp (e2 e1 : edge_spec) : edge_spec :=
  mk_edge (ed_id e1) (ed_src e1) (ed_dst e2)
          (ed_a e2 * ed_a e1) (ed_a e2 * ed_b e1 + ed_b e2).

Lemma edge_comp_slope : forall e1 e2 : edge_spec,
  ed_a (edge_comp e2 e1) == ed_a e2 * ed_a e1.
Proof. intros e1 e2. reflexivity. Qed.

Lemma edge_comp_b : forall e1 e2 : edge_spec,
  ed_b (edge_comp e2 e1) == ed_a e2 * ed_b e1 + ed_b e2.
Proof. intros e1 e2. reflexivity. Qed.

(* 主件：复合边的 eps 映射 = 两边映射的仿射复合（路径语义正确性） *)
Theorem edge_compound_affine : forall (e1 e2 : edge_spec) (x : Q),
  edge_map (edge_comp e2 e1) x == edge_map e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* 复合合法性：两边斜率正 ⟹ 复合斜率恒正 *)
Theorem edge_comp_legal : forall e1 e2 : edge_spec,
  QltT 0 (ed_a e1) -> QltT 0 (ed_a e2) -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H1 H2. apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (ed_a e2) (ed_a e1)
           (QltT_to_Qlt 0 (ed_a e2) H2) (QltT_to_Qlt 0 (ed_a e1) H1)).
Qed.

(* 路径合法性的线性（布尔）判定器：两段路径 *)
Definition path2_ok (e2 e1 : edge_spec) : bool :=
  andb (edge_ok e1) (edge_ok e2).

(* 判定器健全性：布尔判真 ⟹ 复合斜率恒正（线性可判定的合法性） *)
Theorem path2_ok_sound : forall e1 e2 : edge_spec,
  Id (path2_ok e2 e1) true -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H. unfold path2_ok, edge_ok in H.
  destruct (Qlt_bool 0 (ed_a e1)) eqn:E1; destruct (Qlt_bool 0 (ed_a e2)) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  apply edge_comp_legal.
  - apply RealSetoid.eq_Id. exact E1.
  - apply RealSetoid.eq_Id. exact E2.
Qed.

(* 温和边的复合仍温和（斜率乘积 ≤ 1）——耗散记账沿路径封闭 *)
Theorem edge_tame_comp : forall e1 e2 : edge_spec,
  Id (edge_tame e1) true -> Id (edge_tame e2) true ->
  Id (edge_tame (edge_comp e2 e1)) true.
Proof.
  intros e1 e2 H1 H2.
  pose proof (edge_tame_spec e1 H1) as [Ha1 Hb1].
  pose proof (edge_tame_spec e2 H2) as [Ha2 Hb2].
  assert (Hc : Qle (ed_a (edge_comp e2 e1)) 1).
  { assert (Ecomm : ed_a (edge_comp e2 e1) == ed_a e1 * ed_a e2).
    { rewrite edge_comp_slope. ring. }
    assert (Hbound : Qle (ed_a e1 * ed_a e2) 1).
    { apply (Qle_trans (ed_a e1 * ed_a e2) (1 * ed_a e2) 1).
      - apply (Qmult_le_compat_r (ed_a e1) 1 (ed_a e2) Hb1).
        apply (Qlt_le_weak 0 (ed_a e2) Ha2).
      - rewrite Qmult_1_l. exact Hb2. }
    apply (uc_qeq_le_l (ed_a e1 * ed_a e2) (ed_a (edge_comp e2 e1)) 1).
    - symmetry. exact Ecomm.
    - exact Hbound. }
  pose proof (edge_comp_legal e1 e2 (Qlt_to_QltT 0 (ed_a e1) Ha1)
                (Qlt_to_QltT 0 (ed_a e2) Ha2)) as Hp.
  pose proof (RealSetoid.Id_eq (Qlt_bool 0 (ed_a (edge_comp e2 e1))) true Hp) as EA.
  pose proof (Qle_to_QleT' (ed_a (edge_comp e2 e1)) 1 Hc) as HcT.
  pose proof (RealSetoid.Id_eq (Qle_bool (ed_a (edge_comp e2 e1)) 1) true HcT) as EB.
  unfold edge_tame, edge_ok.
  apply RealSetoid.eq_Id.
  rewrite EA. rewrite EB. reflexivity.
Qed.

(* ============================================================ *)
(* §5 件 4：耗散记账 path_dissipation                                *)
(*   币制语义：eps 是守恒量——每次兑换 eps_in = eps_out + 耗散；        *)
(*   耗散沿路径可加（簿记无重计/无凭空铸造）；                        *)
(*   温和边（a≤1）的耗散对入参 eps 单调（大额兑换耗散更大）。          *)
(* ============================================================ *)

(* 币制守恒恒等式 *)
Theorem diss_conservation : forall (e : edge_spec) (x : Q),
  x == edge_map e x + edge_diss e x.
Proof.
  intros e x. unfold edge_diss, edge_map. ring.
Qed.

(* 路径耗散可加：复合路径总耗散 = 段耗散之和（ telescoping 恒等式） *)
Theorem path_dissipation_additive : forall (e1 e2 : edge_spec) (x : Q),
  edge_diss (edge_comp e2 e1) x == edge_diss e1 x + edge_diss e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_diss, edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* 路径耗散单调：温和边 ⟹ 入参 eps 越大耗散越大 *)
Theorem path_dissipation_mono : forall (e : edge_spec) (x y : Q),
  Id (edge_tame e) true -> Qle y x -> Qle (edge_diss e y) (edge_diss e x).
Proof.
  intros e x y Ht Hyx.
  pose proof (edge_tame_spec e Ht) as [Ha Hb].
  assert (H1a : Qle 0 (1 - ed_a e)).
  { exact (uc_le_opp_shift (ed_a e) 1 Hb). }
  assert (Hxy : Qle 0 (x - y)).
  { exact (uc_le_opp_shift y x Hyx). }
  assert (Hprod : Qle 0 ((1 - ed_a e) * (x - y))).
  { apply (Qle_trans 0 (0 * (x - y)) ((1 - ed_a e) * (x - y))).
    - apply uc_qeq_le. ring.
    - apply (Qmult_le_compat_r 0 (1 - ed_a e) (x - y) H1a Hxy). }
  assert (Heq : edge_diss e x == edge_diss e y + (1 - ed_a e) * (x - y)).
  { unfold edge_diss, edge_map, Qminus. ring. }
  rewrite Heq.
  apply (Qle_trans (edge_diss e y)
                   (edge_diss e y + 0)
                   (edge_diss e y + (1 - ed_a e) * (x - y))).
  - apply (uc_qeq_le_r (edge_diss e y) (edge_diss e y + 0) (edge_diss e y)).
    + ring.
    + apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hprod].
Qed.

(* 路径级推论：两段温和边复合后耗散仍单调 *)
Theorem path_dissipation_mono_compound : forall (e1 e2 : edge_spec) (x y : Q),
  Id (edge_tame e1) true -> Id (edge_tame e2) true -> Qle y x ->
  Qle (edge_diss (edge_comp e2 e1) y) (edge_diss (edge_comp e2 e1) x).
Proof.
  intros e1 e2 x y H1 H2 Hyx.
  apply (path_dissipation_mono (edge_comp e2 e1) x y).
  - apply edge_tame_comp; assumption.
  - exact Hyx.
Qed.

(* ============================================================ *)
(* §6 件 5：借据 iou——查询未命中签发缺口义务（可再入）                 *)
(*   对照宪法 check_claim 的 inr 拒绝码形态：resolve 的 inr 载荷即借据。*)
(*   命中 = 可执行证书链（格式接续 + 斜率正 + 耗散在预算内 + 出参正）；  *)
(*   未命中 = 借据（缺口 from→to、耗散预算 δ、eps 槽位、回指查询 id）。  *)
(* ============================================================ *)

Record query : Set := mk_query {
  qr_id : nat;        (* 查询 id *)
  qr_from : nat;      (* 持有格式 *)
  qr_to : nat;        (* 需求格式 *)
  qr_eps : Q;         (* 入参 eps（持券槽位） *)
  qr_delta : Q        (* 耗散预算 δ *)
}.

Record cwe_iou : Set := cwe_mk_iou {
  cwe_iou_from : nat;     (* 缺口源格式 *)
  cwe_iou_to : nat;       (* 缺口目标格式 *)
  cwe_iou_eps : Q;        (* 待重演的 eps 槽位 *)
  cwe_iou_delta : Q;      (* 耗散预算 δ *)
  cwe_iou_ref : nat       (* 回指查询 id：证成后新边长入图谱 *)
}.

(* 借据签发：查询的缺口义务（未命中的唯一产物，不报错） *)
Definition iou_issue (q : query) : cwe_iou :=
  cwe_mk_iou (qr_from q) (qr_to q) (qr_eps q) (qr_delta q) (qr_id q).

(* 布尔门：true 发 Id b true 证，false 发 (Id b false, 借据) 载荷 *)
Definition bool_gate (b : bool) (w : cwe_iou) : Or (Id b true) (And (Id b false) cwe_iou) :=
  match b as x return Or (Id x true) (And (Id x false) cwe_iou) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, w)
  end.

(* 五道门（Defined 可执行）：格式接续 src/dst、斜率正、耗散在预算内、出参正 *)
Definition gate_src (e : edge_spec) (q : query)
  : Or (Id (Nat.eqb (ed_src e) (qr_from q)) true)
       (And (Id (Nat.eqb (ed_src e) (qr_from q)) false) cwe_iou) :=
  bool_gate (Nat.eqb (ed_src e) (qr_from q)) (iou_issue q).

Definition gate_dst (e : edge_spec) (q : query)
  : Or (Id (Nat.eqb (ed_dst e) (qr_to q)) true)
       (And (Id (Nat.eqb (ed_dst e) (qr_to q)) false) cwe_iou) :=
  bool_gate (Nat.eqb (ed_dst e) (qr_to q)) (iou_issue q).

Definition gate_slope (e : edge_spec) (q : query)
  : Or (Id (Qlt_bool 0 (ed_a e)) true)
       (And (Id (Qlt_bool 0 (ed_a e)) false) cwe_iou) :=
  bool_gate (Qlt_bool 0 (ed_a e)) (iou_issue q).

Definition gate_diss (e : edge_spec) (q : query)
  : Or (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
       (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) false) cwe_iou) :=
  bool_gate (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) (iou_issue q).

Definition gate_pos (e : edge_spec) (q : query)
  : Or (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true)
       (And (Id (Qlt_bool 0 (edge_map e (qr_eps q))) false) cwe_iou) :=
  bool_gate (Qlt_bool 0 (edge_map e (qr_eps q))) (iou_issue q).

(* 命中证书：五证包（全 Set 层 Id-of-bool，可提取） *)
Definition hit_cert (e : edge_spec) (q : query) : Set :=
  And (And (Id (Nat.eqb (ed_src e) (qr_from q)) true)
           (Id (Nat.eqb (ed_dst e) (qr_to q)) true))
      (And (Id (Qlt_bool 0 (ed_a e)) true)
           (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
                (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true))).

(* 单边兑换判定：全过发证书，任一门不过发借据（inr 带载荷） *)
Definition resolve1 (e : edge_spec) (q : query) : Or (hit_cert e q) cwe_iou :=
  match gate_src e q with
  | inr p => inr (snd p)
  | inl h1 =>
    match gate_dst e q with
    | inr p => inr (snd p)
    | inl h2 =>
      match gate_slope e q with
      | inr p => inr (snd p)
      | inl h3 =>
        match gate_diss e q with
        | inr p => inr (snd p)
        | inl h4 =>
          match gate_pos e q with
          | inr p => inr (snd p)
          | inl h5 => inl (((h1, h2), (h3, (h4, h5))))
          end
        end
      end
    end
  end.

(* Nat.eqb 判真 → Leibniz 相等的 Set 层 Id 桥 *)
Lemma nat_eqb_id : forall (x y : nat), Id (Nat.eqb x y) true -> Id x y.
Proof.
  intro x. induction x as [| x IH]; intros y H; destruct y as [| y]; simpl in H.
  - apply id_refl.
  - inversion H.
  - inversion H.
  - apply (RealSetoid.eq_Id (Nat.succ x) (Nat.succ y)).
    f_equal. apply RealSetoid.Id_eq. apply IH. exact H.
Qed.

(* 命中证书的语义形态：格式接续的直证 + Q 层事实 *)
Theorem hit_cert_honest : forall (e : edge_spec) (q : query) (w : hit_cert e q),
  And (And (Id (ed_src e) (qr_from q)) (Id (ed_dst e) (qr_to q)))
      (And (QltT 0 (ed_a e))
           (And (QleT' (edge_diss e (qr_eps q)) (qr_delta q))
                (QltT 0 (edge_map e (qr_eps q))))).
Proof.
  intros e q [[h1 h2] [h3 [h4 h5]]].
  split; [split | split].
  - apply nat_eqb_id. exact h1.
  - apply nat_eqb_id. exact h2.
  - exact h3.
  - split; [exact h4 | exact h5].
Qed.

(* 布尔门拒绝分支的载荷恒为借据本身 *)
Lemma bool_gate_inr : forall (b : bool) (w : cwe_iou) (p1 : Id b false) (p2 : cwe_iou),
  Id (bool_gate b w) (inr (p1, p2)) -> Id p2 w.
Proof.
  intros b w p1 p2 H.
  pose proof (RealSetoid.Id_eq (bool_gate b w) (inr (p1, p2)) H) as E.
  unfold bool_gate in E. destruct b; simpl in E.
  - discriminate E.
  - injection E as E1 E2.
    apply RealSetoid.eq_Id. symmetry. exact E2.
Qed.

(* 件 5 主定理：单边未命中 ⟹ 借据携带缺口义务（from/to/eps/δ 全回指查询） *)
Theorem resolve1_inr_fields : forall (e : edge_spec) (q : query) (r : cwe_iou),
  Id (resolve1 e q) (inr r) ->
  And (And (Id (cwe_iou_from r) (qr_from q)) (Id (cwe_iou_to r) (qr_to q)))
      (And (Id (cwe_iou_eps r) (qr_eps q)) (Id (cwe_iou_delta r) (qr_delta q))).
Proof.
  intros e q r H. unfold resolve1 in H.
  destruct (gate_src e q) as [h1 | [p11 p12]] eqn:Ep1;
    cbv beta iota in H.
  - destruct (gate_dst e q) as [h2 | [p21 p22]] eqn:Ep2;
      cbv beta iota in H.
    + destruct (gate_slope e q) as [h3 | [p31 p32]] eqn:Ep3;
        cbv beta iota in H.
      * destruct (gate_diss e q) as [h4 | [p41 p42]] eqn:Ep4;
          cbv beta iota in H.
        -- destruct (gate_pos e q) as [h5 | [p51 p52]] eqn:Ep5;
             cbv beta iota in H.
           ++ pose proof (RealSetoid.Id_eq _ _ H) as E. discriminate E.
           ++ pose proof (RealSetoid.Id_eq _ _ H) as E.
              injection E as E1.
              pose proof (bool_gate_inr _ _ _ _
                (RealSetoid.eq_Id _ _ Ep5)) as Hpay.
              rewrite <- E1. rewrite Hpay.
              split; [split; reflexivity | split; reflexivity].
        -- pose proof (RealSetoid.Id_eq _ _ H) as E.
           injection E as E1.
           pose proof (bool_gate_inr _ _ _ _
             (RealSetoid.eq_Id _ _ Ep4)) as Hpay.
           rewrite <- E1. rewrite Hpay.
           split; [split; reflexivity | split; reflexivity].
      * pose proof (RealSetoid.Id_eq _ _ H) as E.
        injection E as E1.
        pose proof (bool_gate_inr _ _ _ _
          (RealSetoid.eq_Id _ _ Ep3)) as Hpay.
        rewrite <- E1. rewrite Hpay.
        split; [split; reflexivity | split; reflexivity].
    + pose proof (RealSetoid.Id_eq _ _ H) as E.
      injection E as E1.
      pose proof (bool_gate_inr _ _ _ _
        (RealSetoid.eq_Id _ _ Ep2)) as Hpay.
      rewrite <- E1. rewrite Hpay.
      split; [split; reflexivity | split; reflexivity].
  - pose proof (RealSetoid.Id_eq _ _ H) as E.
    injection E as E1.
    pose proof (bool_gate_inr _ _ _ _
      (RealSetoid.eq_Id _ _ Ep1)) as Hpay.
    rewrite <- E1. rewrite Hpay.
    split; [split; reflexivity | split; reflexivity].
Qed.

(* 图谱扫描（Defined 可执行）：按格式键 (from,to) 找第一条服务边 *)
Fixpoint find_serving (g : list edge_spec) (f t : nat) : option edge_spec :=
  match g with
  | nil => None
  | e :: g' =>
      match Nat.eqb (ed_src e) f with
      | true =>
          match Nat.eqb (ed_dst e) t with
          | true => Some e
          | false => find_serving g' f t
          end
      | false => find_serving g' f t
      end
  end.

Lemma find_serving_cons_some : forall (e : edge_spec) (g : list edge_spec) (f t : nat),
  Nat.eqb (ed_src e) f = true -> Nat.eqb (ed_dst e) t = true ->
  Id (find_serving (e :: g) f t) (Some e).
Proof.
  intros e g f t H1 H2. simpl.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* 图谱级兑换：Some e 走单边判定，None 签发借据 *)
Definition resolve_opt (o : option edge_spec) (q : query)
  : Or (sigT (fun e => hit_cert e q)) cwe_iou :=
  match o with
  | None => inr (iou_issue q)
  | Some e =>
      match resolve1 e q with
      | inl w => inl (existT _ e w)
      | inr r => inr r
      end
  end.

Definition resolve (g : list edge_spec) (q : query)
  : Or (sigT (fun e => hit_cert e q)) cwe_iou :=
  resolve_opt (find_serving g (qr_from q) (qr_to q)) q.

Lemma resolve_opt_some : forall (e : edge_spec) (q : query) (w : hit_cert e q),
  Id (resolve1 e q) (inl w) ->
  Id (resolve_opt (Some e) q) (inl (existT _ e w)).
Proof.
  intros e q w H. unfold resolve_opt. rewrite H. reflexivity.
Qed.

(* 判定总全性：任何查询必得命中或借据（对照宪法 check_claim_total） *)
Theorem resolve_total : forall (g : list edge_spec) (q : query),
  Or (sigT (fun e => sigT (fun w => Id (resolve g q) (inl (existT _ e w)))))
     (sigT (fun r => Id (resolve g q) (inr r))).
Proof.
  intros g q. unfold resolve, resolve_opt.
  destruct (find_serving g (qr_from q) (qr_to q)) as [e |].
  - destruct (resolve1 e q) as [w | r].
    + left. exists e. exists w. reflexivity.
    + right. exists r. reflexivity.
  - right. exists (iou_issue q). reflexivity.
Qed.

(* 件 5 图谱级形态：未命中 ⟹ 借据携带缺口义务 *)
Theorem resolve_miss_iou : forall (g : list edge_spec) (q : query) (r : cwe_iou),
  Id (resolve g q) (inr r) ->
  And (And (Id (cwe_iou_from r) (qr_from q)) (Id (cwe_iou_to r) (qr_to q)))
      (And (Id (cwe_iou_eps r) (qr_eps q)) (Id (cwe_iou_delta r) (qr_delta q))).
Proof.
  intros g q r H. unfold resolve, resolve_opt in H.
  destruct (find_serving g (qr_from q) (qr_to q)) as [e |].
  - destruct (resolve1 e q) as [w | r0] eqn:Eq; cbv beta iota in H.
    + pose proof (RealSetoid.Id_eq _ _ H) as E. discriminate E.
    + pose proof (RealSetoid.Id_eq _ _ H) as E.
      injection E as E1.
      pose proof (resolve1_inr_fields e q r0
        (RealSetoid.eq_Id _ _ Eq)) as [[Hf Ht] [He Hd]].
      rewrite <- E1.
      split; [split; assumption | split; assumption].
  - pose proof (RealSetoid.Id_eq _ _ H) as E.
    injection E as E1. rewrite <- E1.
    split; [split; reflexivity | split; reflexivity].
Qed.

(* 命中健全性：命中 ⟹ 出参 eps 严格正且耗散在预算内（可执行证书语义） *)
Theorem resolve_hit_sound : forall (g : list edge_spec) (q : query)
                                   (e : edge_spec) (w : hit_cert e q),
  Id (resolve g q) (inl (existT _ e w)) ->
  And (QltT 0 (edge_map e (qr_eps q)))
      (QleT' (edge_diss e (qr_eps q)) (qr_delta q)).
Proof.
  intros g q e w _. destruct w as [_ [_ [h4 h5]]].
  split; assumption.
Qed.

(* ============================================================ *)
(* 件 5b：借据再入——redeem（证成）与 reissue（义务持久）              *)
(*   redeem io e = e 若闭 io 的缺口则发证书（新边可长入图谱）；        *)
(*   兑换不过门则借据原样再入（义务不灭，可携新边重试）。              *)
(* ============================================================ *)

Definition iou_query (io : cwe_iou) : query :=
  mk_query (cwe_iou_ref io) (cwe_iou_from io) (cwe_iou_to io) (cwe_iou_eps io) (cwe_iou_delta io).

Definition cwe_redeem (io : cwe_iou) (e : edge_spec) : Or (hit_cert e (iou_query io)) cwe_iou :=
  resolve1 e (iou_query io).

(* 再入：cwe_redeem 拒绝 ⟹ 返回借据的缺口字段与原借据逐位相同（义务持久） *)
Theorem redeem_reissue : forall (io : cwe_iou) (e : edge_spec) (r : cwe_iou),
  Id (cwe_redeem io e) (inr r) ->
  And (And (Id (cwe_iou_from r) (cwe_iou_from io))
           (And (Id (cwe_iou_to r) (cwe_iou_to io)) (Id (cwe_iou_eps r) (cwe_iou_eps io))))
      (Id (cwe_iou_delta r) (cwe_iou_delta io)).
Proof.
  intros io e r H.
  pose proof H as H'.
  pose proof (resolve1_inr_fields e (iou_query io) r H') as [[Hf Ht] [He Hd]].
  split.
  - split; [exact Hf | split; [exact Ht | exact He]].
  - exact Hd.
Qed.

(* 证成：借据被新边闭合 ⟹ 新边长入图谱且原查询命中（图谱成长定理） *)
Theorem redeem_closes : forall (io : cwe_iou) (e : edge_spec) (g : list edge_spec)
                               (w : hit_cert e (iou_query io)),
  Id (cwe_redeem io e) (inl w) ->
  sigT (fun w2 => Id (resolve (e :: g) (iou_query io)) (inl w2)).
Proof.
  intros io e g w Hred.
  destruct w as [[h1 h2] [h3 [h4 h5]]].
  pose proof Hred as Hred'.
  pose proof (RealSetoid.Id_eq (Nat.eqb (ed_src e) (qr_from (iou_query io))) true
                h1) as E1.
  pose proof (RealSetoid.Id_eq (Nat.eqb (ed_dst e) (qr_to (iou_query io))) true
                h2) as E2.
  pose proof (find_serving_cons_some e g (qr_from (iou_query io))
                (qr_to (iou_query io)) E1 E2) as Hfs.
  pose proof (RealSetoid.Id_eq _ _ Hfs) as Efs.
  pose proof (resolve_opt_some e (iou_query io)
              (((h1, h2), (h3, (h4, h5)))) Hred') as Hw2.
  exists (existT (fun e0 : edge_spec => hit_cert e0 (iou_query io)) e
                 (((h1, h2), (h3, (h4, h5))))).
  unfold resolve. rewrite Efs. exact Hw2.
Qed.

(* ============================================================ *)
(* 判定报文（非依赖形态：无 sigT，可整体提取；vm_compute 友好）        *)
(* ============================================================ *)

Inductive resolve_verdict : Set :=
| rv_hit : edge_spec -> Q -> resolve_verdict
| rv_miss : cwe_iou -> resolve_verdict.

Definition resolve_report (g : list edge_spec) (q : query) : resolve_verdict :=
  match find_serving g (qr_from q) (qr_to q) with
  | None => rv_miss (iou_issue q)
  | Some e =>
      match resolve1 e q with
      | inl w => rv_hit e (Qred (edge_map e (qr_eps q)))
      | inr r => rv_miss r
      end
  end.

(* ============================================================ *)
(* §7 件 6：vm_compute 数值自测——3 边图谱 eps/2→eps/4→eps/8 链        *)
(*   图谱 = 3 条原始半耗散边 + 2 条复合边（复合封闭性使寻路可达）。      *)
(* ============================================================ *)

(* 原始边：fmt0→fmt1→fmt2→fmt3，每段 eps 减半（a=1/2, b=0，零注入） *)
Definition e_h1 : edge_spec := mk_edge 1 0 1 (1#2) 0.
Definition e_h2 : edge_spec := mk_edge 2 1 2 (1#2) 0.
Definition e_h3 : edge_spec := mk_edge 3 2 3 (1#2) 0.

(* 复合边长入图谱：ec12 : fmt0→fmt2 斜率 1/4；ec123 : fmt0→fmt3 斜率 1/8 *)
Definition ec12 : edge_spec := edge_comp e_h2 e_h1.
Definition ec123 : edge_spec := edge_comp e_h3 ec12.

Definition atlas3 : list edge_spec := e_h1 :: e_h2 :: e_h3 :: ec12 :: ec123 :: nil.

(* 查询 7：持 fmt0、eps 槽位 1，要 fmt3，耗散预算 δ=1 —— 命中 ec123 *)
Definition q_chain : query := mk_query 7 0 3 1 1.
(* 查询 8：fmt3→fmt0 无任何边 —— 未命中，签发借据 *)
Definition q_back : query := mk_query 8 3 0 1 1.
(* 查询 9：fmt0→fmt3 但预算 δ=1/2 —— 耗散 7/8 超预算，借据（缺口义务） *)
Definition q_tight : query := mk_query 9 0 3 1 (1#2).

(* 链命中：出参 eps = 1/8（eps→eps/8），证书可执行 *)
Theorem demo_chain_hit : Id (resolve_report atlas3 q_chain) (rv_hit ec123 (1#8)).
Proof. vm_compute. reflexivity. Qed.

(* 路径耗散值：1 − 1/8 = 7/8（可加记账：1/2 + (3/4) 段耗散之和） *)
Theorem demo_diss_total : Id (Qred (edge_diss ec123 1)) (7#8).
Proof. vm_compute. reflexivity. Qed.

Theorem demo_diss_steps : edge_diss ec123 1
  == edge_diss ec12 1 + edge_diss e_h3 (edge_map ec12 1).
Proof. vm_compute. reflexivity. Qed.

(* 币制守恒恒等式的数值实例：1 = 1/8 + 7/8 *)
Theorem demo_conservation : 1 == edge_map ec123 1 + edge_diss ec123 1.
Proof. vm_compute. reflexivity. Qed.

(* 反向查询无边：未命中 ⟹ 借据（缺口 fmt3→fmt0，回指查询 8） *)
Theorem demo_miss_back : Id (resolve_report atlas3 q_back)
  (rv_miss (cwe_mk_iou 3 0 1 1 8)).
Proof. vm_compute. reflexivity. Qed.

(* 预算不足：耗散 7/8 > δ=1/2 ⟹ 借据（缺口 fmt0→fmt3，回指查询 9） *)
Theorem demo_tight_iou : Id (resolve_report atlas3 q_tight)
  (rv_miss (cwe_mk_iou 0 3 1 (1#2) 9)).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 件 5b 数值自测：借据再入——好边兑换闭合缺口，新边长入图谱          *)
(* ============================================================ *)

Definition demo_io_tight : cwe_iou := cwe_mk_iou 0 3 1 (1#2) 9.

(* 好边：fmt0→fmt3 斜率 15/16 —— 耗散 1/16 ≤ 1/2，出参 15/16 > 0 *)
Definition e_good : edge_spec := mk_edge 4 0 3 (15#16) 0.

(* cwe_redeem：借据 demo_io_tight 被 e_good 证成（五证全过） *)
Definition cert_good : hit_cert e_good (iou_query demo_io_tight) :=
  ((@id_refl bool true, @id_refl bool true),
   (@id_refl bool true, (@id_refl bool true, @id_refl bool true))).

Theorem demo_redeem_ok : Id (cwe_redeem demo_io_tight e_good) (inl cert_good).
Proof. vm_compute. reflexivity. Qed.

(* redeem_closes 数值实例：新边长入图谱后，原查询 9 命中 e_good *)
Definition atlas4 : list edge_spec := e_good :: atlas3.

Theorem demo_growth_closes :
  Id (resolve_report atlas4 q_tight) (rv_hit e_good (15#16)).
Proof. vm_compute. reflexivity. Qed.

(* 再入形态数值实例：坏边（负截距吞掉 eps 槽位）证不成，借据原样返回 *)
Definition e_bad : edge_spec := mk_edge 5 0 3 (15#16) (-1).

Theorem demo_redeem_reissue :
  sigT (fun r => Id (cwe_redeem demo_io_tight e_bad) (inr r)).
Proof.
  exists (iou_issue (iou_query demo_io_tight)).
  unfold cwe_redeem. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §8 判定报文输出（G3 自测样例源）                                  *)
(* ============================================================ *)

Eval vm_compute in resolve_report atlas3 q_chain.
Eval vm_compute in resolve_report atlas3 q_back.
Eval vm_compute in resolve_report atlas3 q_tight.
Eval vm_compute in resolve_report atlas4 q_tight.
Eval vm_compute in edge_diss ec123 1.
Eval vm_compute in bond_check (mk_bond 1 (3#2) (1#4) 0).
Eval vm_compute in edge_check e_good.

(* ---------- UpStopTime ---------- *)
Module StopTime.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Extraction.
Import BudgetReal.
Import Constitution.
Set Extraction Output Directory ".".
(* ============================================================ *)
(* UpStopTime.v —— 可证书化停时原语 + GuardedChain 守恒击穿链        *)
(*                                                              *)
(* 理论来源：成果存档/圆桌会议/ROUNDTABLE-六席圆桌实验-20260907.md    *)
(*   头部候选「可证书化停时原语」——席 4 BDA 击穿反解 × 席 6 SPC      *)
(*   封口 t* × 席 2 GATC 账本停时的三席收敛格点的 Coq 立项；          *)
(*   方法论 §5：GuardedChain = 生产性非良基（CoInductive 每步        *)
(*   携带预算见证），席 2 终稿的阈值策略双目标占优定理离散形态。       *)
(*                                                              *)
(* 五件交付：                                                    *)
(*   件 1  GChain/grun      GuardedChain 守恒击穿链                 *)
(*                         （CoInductive + CoFixpoint 生成器，       *)
(*                          每步产出构造子 = 守恒；预算逐项递减）     *)
(*   件 2  guarded_breaks   生产性⟹健全性：预算严格递降的链必触底     *)
(*                         （nat 良基递降的构造性击穿）+ 触底值推论    *)
(*   件 3  minimal_stoptime 最小停时 N* = min{N : c0·(1−κ)^N < eps} *)
(*                         （stsearch 线性搜索；3a 最小性 + 3b 上界单调） *)
(*   件 4  st_dominance     阈值策略双目标占优（离散形态，纯序代数）   *)
(*   件 5  unguarded_*      反面对照：无见证恒值链永不触底，           *)
(*                         与 GuardedChain 分离（无预算⟹停时不存在）  *)
(*                                                              *)
(* 数学核心：q_decay_breaks（UpConstitution）保证存在性；            *)
(*   stsearch 线性搜索输出最小跨阈指数 + 逐前项未跨阈证书；           *)
(*   阈值策略在证书可测策略类中同时极小化合并次数与无效服务数。        *)
(*                                                              *)
(* 层位纪律：语句全 Set 层（Id/NatLe/NatLt/QltT/QleT'/QId/sigT/     *)
(*   And/Or/Not），无 Prop 泄露；纯构造性禁词零出现；全部 Qed。      *)
(* ============================================================ *)


Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 本地桥（nat 序 / bool 反映 / Q 换形；宪法席解法口径）          *)
(* ============================================================ *)

(* NatLt 双向桥（NatLt = Id (Nat.ltb n m) true；       *)
(*   库内 natlt_elim/intro 困在 LiveCore section 不可达，本地重建）   *)
Lemma st_natlt_drop : forall n m : nat, NatLt n m -> (n < m)%nat.
Proof.
intros n m H. apply (proj1 (Nat.ltb_lt n m)).
apply RealSetoid.Id_eq. exact H.
Qed.

Lemma st_natlt_lift : forall n m : nat, (n < m)%nat -> NatLt n m.
Proof.
intros n m H. apply RealSetoid.eq_Id. apply (proj2 (Nat.ltb_lt n m)).
exact H.
Qed.

(* QltT 的 bool false 换形：未跨阈 ⟹ 阈值 ≤ 当前值（件 3a 最小性用） *)
Lemma st_qlt_false_ge : forall x y : Q, Id (Qlt_bool x y) false -> QleT' y x.
Proof.
intros x y Hf.
destruct (Q_dec x y) as [[H1 | H2] | H3].
- exfalso.
  assert (Ht : QltT x y) by (apply Qlt_to_QltT; exact H1).
  pose proof (id_trans (id_sym Hf) Ht) as Hc. inversion Hc.
- apply uc_qleT_of_ltT. apply Qlt_to_QltT. exact H2.
- apply Qle_to_QleT'. apply uc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* QId（Qeq_bool 反映）左元换形：x == y 且 y < z ⟹ x < z *)
Definition QId (x y : Q) : Set := Id (Qeq_bool x y) true.

Lemma st_qid_refl : forall x : Q, QId x x.
Proof. intro x. apply sf_qeq_id. apply Qeq_refl. Qed.

Lemma st_qid_trans : forall a b c : Q, QId a b -> QId b c -> QId a c.
Proof.
intros a b c H1 H2. apply sf_qeq_id.
apply (Qeq_trans a b c (sf_id_qeq a b H1) (sf_id_qeq b c H2)).
Qed.

Lemma st_qltT_qid_l : forall x y z : Q, QId x y -> QltT y z -> QltT x z.
Proof.
intros x y z Hq Hlt. apply Qlt_to_QltT.
apply (uc_qeq_lt_l y x z (Qeq_sym x y (sf_id_qeq x y Hq))).
apply QltT_to_Qlt. exact Hlt.
Qed.

(* QltT ⟹ Qle（Prop 序前提位；Qlt_le_weak 宪法席已验证口径） *)
Lemma st_qle_of_ltT : forall x y : Q, QltT x y -> Qle x y.
Proof. intros x y H. apply Qlt_le_weak. apply QltT_to_Qlt. exact H. Qed.

(* 1 − k ≤ 1（由 0 ≤ k；Qplus_le_compat + Qopp 换形，先例口径） *)
Lemma st_qle_one_minus : forall k : Q, Qle 0 k -> Qle (1 - k) 1.
Proof.
intros k Hk.
apply (uc_qeq_le_l (1 + (- k)) (1 - k)%Q 1%Q).
- reflexivity.
- apply (uc_qeq_le_r (1 + 0)%Q 1%Q (1 + (- k))%Q).
  + apply Qplus_0_r.
  + apply Qplus_le_compat.
    * apply Qle_refl.
    * apply (uc_opp_le_shift k Hk).
Qed.

(* nat 最小值（可提取；leb 判定） *)
Definition stmin (a b : nat) : nat := if Nat.leb a b then a else b.

Lemma stmin_le_l : forall a b : nat, NatLe b a -> Id (stmin a b) b.
Proof.
intros a b H. apply NatLe_drop in H. unfold stmin.
destruct (Nat.leb a b) eqn:E.
- apply Nat.leb_le in E. assert (Heq : a = b) by lia.
  rewrite Heq. reflexivity.
- reflexivity.
Qed.

Lemma stmin_le_r : forall a b : nat, NatLe a b -> Id (stmin a b) a.
Proof.
intros a b H. apply NatLe_drop in H. unfold stmin.
destruct (Nat.leb a b) eqn:E.
- reflexivity.
- apply Nat.leb_gt in E. assert (Heq : a = b) by lia.
  rewrite Heq. reflexivity.
Qed.

(* Id 上的 nat ≤（相等即 ≤） *)
Lemma st_natle_of_id : forall n m : nat, Id n m -> NatLe n m.
Proof.
intros n m H. apply NatLe_lift. apply Nat.leb_le.
assert (E : n = m) by (apply RealSetoid.Id_eq; exact H).
rewrite E. apply Nat.leb_refl.
Qed.

(* ============================================================ *)
(* §1 件 1：GuardedChain 守恒击穿链                                *)
(*   CoInductive：非良基类型；每步 gstep 产出构造子 = 生产性守恒。    *)
(*   gstop：触底节点（剩余预算、终值）；触底后预算清零、终值保持。    *)
(*   grun：CoFixpoint 生成器（守卫条件：递归调用在 gstep 之下），    *)
(*   预算参数逐层严格递减——生产性由 Coq 守卫检查器静态强制。         *)
(* ============================================================ *)

CoInductive GChain : Set :=
| gstop : nat -> Q -> GChain
| gstep : nat -> Q -> GChain -> GChain.

(* 守恒生成器：几何衰减链（率 k、剩余预算 b、累积值 c） *)
CoFixpoint grun (k : Q) (b : nat) (c : Q) : GChain :=
  match b with
  | O => gstop 0 c
  | Datatypes.S b' => gstep (Datatypes.S b') c (grun k b' (c * (1 - k)))
  end.

(* 投影：链头预算 / 链头累积值 *)
Definition gchain_budget (ch : GChain) : nat :=
  match ch with gstop b _ => b | gstep b _ _ => b end.

Definition gchain_head (ch : GChain) : Q :=
  match ch with gstop _ c => c | gstep _ c _ => c end.

(* 观察者：深度 n 处的预算 / 累积值 / 触底检测 *)
(*   预算口径（清零制）：gstop 触底后预算清零——账本清偿完毕。        *)
Fixpoint gbudget_at (n : nat) (ch : GChain) : nat :=
  match n with
  | O => gchain_budget ch
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => 0
      | gstep _ _ tl => gbudget_at m tl
      end
  end.

(*   终值口径（保持制）：gstop 触底后累积值冻结。                   *)
Fixpoint ghead_at (n : nat) (ch : GChain) : Q :=
  match n with
  | O => gchain_head ch
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => gchain_head ch
      | gstep _ _ tl => ghead_at m tl
      end
  end.

(*   触底检测：n 步内出现 gstop，或出现预算已尽的 gstep 节点。       *)
Fixpoint gbottom_at (n : nat) (ch : GChain) : bool :=
  match n with
  | O =>
      match ch with
      | gstop _ _ => true
      | gstep b _ _ => Nat.leb b 0
      end
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => true
      | gstep b _ tl => if Nat.leb b 0 then true else gbottom_at m tl
      end
  end.

(* 参照值序列：c·(1−k)^n 的迭代形（与 grun 逐层同步收缩） *)
Fixpoint gval (k : Q) (c : Q) (n : nat) : Q :=
  match n with
  | O => c
  | Datatypes.S m => gval k (c * (1 - k)) m
  end.

(* ---- 件 1 引理组：守恒性 / 预算单调 / 终值 ----- *)

(* 生成器头投影：链头预算即生成预算（destruct 后 match 强制 cofix 展开） *)
Lemma grun_budget : forall (k : Q) (b : nat) (c : Q),
  Id (gchain_budget (grun k b c)) b.
Proof.
intros k b c. destruct b; reflexivity.
Qed.

Lemma grun_head : forall (k : Q) (b : nat) (c : Q),
  Id (gchain_head (grun k b c)) c.
Proof.
intros k b c. destruct b; reflexivity.
Qed.

(* 预算单调：深度 n ≤ b 处预算 = b − n（每步严格递减的逐点形态） *)
Lemma grun_budget_at : forall (k : Q) (n : nat) (b : nat) (c : Q),
  NatLe n b -> Id (gbudget_at n (grun k b c)) (b - n)%nat.
Proof.
intros k n. induction n as [| n IH]; intros b c Hn.
- destruct b as [| b']; reflexivity.
- destruct b as [| b'].
  + apply NatLe_drop in Hn. lia.
  + change (gbudget_at (Datatypes.S n) (grun k (Datatypes.S b') c))
      with (gbudget_at n (grun k b' (c * (1 - k)))).
    replace (Datatypes.S b' - Datatypes.S n)%nat with (b' - n)%nat by lia.
    apply IH. apply NatLe_lift. apply NatLe_drop in Hn. lia.
Qed.

(* 终值轨迹：深度 n ≤ b 处累积值 = 参照值序列第 n 项 *)
Lemma grun_head_at : forall (k : Q) (n : nat) (b : nat) (c : Q),
  NatLe n b -> Id (ghead_at n (grun k b c)) (gval k c n).
Proof.
intros k n. induction n as [| n IH]; intros b c Hn.
- destruct b as [| b']; reflexivity.
- destruct b as [| b'].
  + apply NatLe_drop in Hn. lia.
  + change (ghead_at (Datatypes.S n) (grun k (Datatypes.S b') c))
      with (ghead_at n (grun k b' (c * (1 - k)))).
    change (gval k c (Datatypes.S n)) with (gval k (c * (1 - k)) n).
    apply IH. apply NatLe_lift. apply NatLe_drop in Hn. lia.
Qed.

(* 乘法结合律（原子变量形——Q-ring 拒含 Qminus 项，先抽变量化引理） *)
Lemma st_mult_assoc_qeq : forall (a b p : Q), (a * b) * p == a * (b * p).
Proof. intros a b p. ring. Qed.

(* 参照值序列 == 幂形：gval k c n == c·(1−k)^n（QId 反映形） *)
Lemma gval_pow_QId : forall (k : Q) (n : nat) (c : Q),
  QId (gval k c n) (c * q_pow (1 - k) n).
Proof.
intros k n. induction n as [| n IH]; intros c.
- replace (q_pow (1 - k) 0) with 1%Q by reflexivity.
  apply sf_qeq_id. apply Qeq_sym. apply Qmult_1_r.
- change (gval k c (Datatypes.S n)) with (gval k (c * (1 - k)) n).
  change (q_pow (1 - k) (Datatypes.S n)) with ((1 - k) * q_pow (1 - k) n).
  assert (H1 : Id (Qeq_bool (gval k (c * (1 - k)) n)
                     ((c * (1 - k)) * q_pow (1 - k) n)) true)
    by exact (IH (c * (1 - k))).
  assert (H2 : Id (Qeq_bool ((c * (1 - k)) * q_pow (1 - k) n)
                     (c * ((1 - k) * q_pow (1 - k) n))) true)
    by (apply sf_qeq_id;
        exact (st_mult_assoc_qeq c (1 - k) (q_pow (1 - k) n))).
  exact (st_qid_trans _ _ _ H1 H2).
Qed.

(* 触底检测单调：n 步内触底 ⟹ 后继步内仍触底 *)
(*   修复记录：不动点观察 gbottom_at (S n) (gstep b ..) 里的 Nat.leb b 0   *)
(*   是卡死项——直接 destruct b，令 leb (S b') 0 ≡ false 定义性归约。     *)
Lemma gbottom_mono : forall (n : nat) (ch : GChain),
  Id (gbottom_at n ch) true -> Id (gbottom_at (Datatypes.S n) ch) true.
Proof.
intros n. induction n as [| n IH]; intros ch H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbottom_at 0%nat (gstep (Datatypes.S b') c tl)) with false in H.
      inversion H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbottom_at (Datatypes.S (Datatypes.S n)) (gstep (Datatypes.S b') c tl))
        with (gbottom_at (Datatypes.S n) tl).
      apply IH.
      change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl) in H.
      exact H.
Qed.

(* 触底 ⟹ 后继深度预算清零（清零制口径；需全程递减前提
   排除「预算 0 仍续步」的空洞链——该前提即 GuardedChain 纪律本体） *)
(*   修复记录：原稿 destruct (Nat.leb b 0) eqn: 留卡死 if，且 Hdec 多传   *)
(*   实参；改为 destruct b + Hdec 单实参 + Id_eq 换形 nat 序后 lia。     *)
Lemma gbottom_true_spend : forall (n : nat) (ch : GChain),
  (forall m : nat, NatLt (gbudget_at (Datatypes.S m) ch) (gbudget_at m ch)) ->
  Id (gbottom_at n ch) true -> Id (gbudget_at (Datatypes.S n) ch) 0%nat.
Proof.
intros n. induction n as [| n IH]; intros ch Hdec H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * (* gstep 0 触底：全程递减在 m=0 要求尾链预算 < 0——空洞链被排除 *)
      exfalso.
      pose proof (Hdec 0%nat) as Hbad.
      change (gbudget_at 1%nat (gstep 0%nat c tl)) with (gbudget_at 0%nat tl)
        in Hbad.
      change (gbudget_at 0%nat (gstep 0%nat c tl)) with 0%nat in Hbad.
      pose proof (proj1 (Nat.ltb_lt (gbudget_at 0%nat tl) 0%nat)
                    (RealSetoid.Id_eq _ _ Hbad)) as Hlt.
      lia.
    * change (gbottom_at 0%nat (gstep (Datatypes.S b') c tl)) with false in H.
      inversion H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * (* gstep 0：同一空洞链排除 *)
      exfalso.
      pose proof (Hdec 0%nat) as Hbad.
      change (gbudget_at 1%nat (gstep 0%nat c tl)) with (gbudget_at 0%nat tl)
        in Hbad.
      change (gbudget_at 0%nat (gstep 0%nat c tl)) with 0%nat in Hbad.
      pose proof (proj1 (Nat.ltb_lt (gbudget_at 0%nat tl) 0%nat)
                    (RealSetoid.Id_eq _ _ Hbad)) as Hlt.
      lia.
    * change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl) in H.
      change (gbudget_at (Datatypes.S (Datatypes.S n)) (gstep (Datatypes.S b') c tl))
        with (gbudget_at (Datatypes.S n) tl).
      apply IH.
      -- (* 递减前提沿 gstep 尾链传输（Hdec 全称量词直接取后继实例） *)
         intros m.
         pose proof (Hdec (Datatypes.S m)) as Hs.
         change (gbudget_at (Datatypes.S (Datatypes.S m)) (gstep (Datatypes.S b') c tl))
           with (gbudget_at (Datatypes.S m) tl) in Hs.
         change (gbudget_at (Datatypes.S m) (gstep (Datatypes.S b') c tl))
           with (gbudget_at m tl) in Hs.
         exact Hs.
      -- exact H.
Qed.

(* 预算尽 ⟹ 触底（无前提形态：检测器计数预算尽的 gstep 节点） *)
Lemma gbottom_true_of_budget0 : forall (n : nat) (ch : GChain),
  Id (gbudget_at n ch) 0%nat -> Id (gbottom_at n ch) true.
Proof.
intros n. induction n as [| n IH]; intros ch H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + change (gbudget_at 0%nat (gstep b c tl)) with b in H.
    rewrite (RealSetoid.Id_eq b 0%nat H). reflexivity.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbudget_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbudget_at n tl) in H.
      change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl).
      apply IH. exact H.
Qed.

(* ---- 件 1 vm_compute 自测（G3 样例输出源之一） ---- *)
(*   grun (1/2) 4 (8/10)：预算 4→3→2→1→0 触底，值 0.8·(1/2)^n 递减 *)
Eval vm_compute in gbudget_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in ghead_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in gbottom_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in gbottom_at 3 (grun (1#2) 4 (8#10)).

Lemma test_grun_budget0 : Id (gbudget_at 4 (grun (1#2) 4 (8#10))) 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_grun_bottom : Id (gbottom_at 4 (grun (1#2) 4 (8#10))) true.
Proof. vm_compute. reflexivity. Qed.

Lemma test_grun_running3 : Id (gbottom_at 3 (grun (1#2) 4 (8#10))) false.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §2 件 2：生产性⟹健全性（消费 UpConstitution.q_decay_breaks）      *)
(*   生产性：CoFixpoint 生成器每步严格递减预算 ⟹ b 步内必触底；        *)
(*   健全性：以 q_decay_breaks 解出的击穿预算 N 作链预算，             *)
(*   链在深度 N 触底且终值 = c0·(1−κ)^N < eps——停时携带证书。         *)
(* ============================================================ *)

(* 生产性 a：守恒链的账本在自身预算处清零（清偿完毕） *)
Corollary guarded_ledger_clears : forall (k : Q) (b : nat) (c : Q),
  Id (gbudget_at b (grun k b c)) 0%nat.
Proof.
intros k b c.
assert (Hzz : Id (b - b)%nat 0%nat)
  by (apply RealSetoid.eq_Id; apply Nat.sub_diag).
exact (id_trans (grun_budget_at k b b c (NatLe_lift b b (Nat.le_refl b))) Hzz).
Qed.

(* 生产性 b：预算严格递减的逐点见证（m < b ⟹ 深度 m+1 处预算更小） *)
Lemma grun_budget_strict : forall (k : Q) (b : nat) (c : Q) (m : nat),
  NatLt m b ->
  NatLt (gbudget_at (Datatypes.S m) (grun k b c)) (gbudget_at m (grun k b c)).
Proof.
intros k b c m Hm. apply NatLe_drop in Hm.
assert (H1 : Id (gbudget_at (Datatypes.S m) (grun k b c)) (b - Datatypes.S m)%nat).
{ apply grun_budget_at. apply NatLe_lift. lia. }
assert (H2 : Id (gbudget_at m (grun k b c)) (b - m)%nat).
{ apply grun_budget_at. apply NatLe_lift. lia. }
apply st_natlt_lift.
rewrite (RealSetoid.Id_eq _ _ H1).
rewrite (RealSetoid.Id_eq _ _ H2).
lia.
Qed.

(* 生产性 c：任意预算 b 的守恒链在深度 b 必触底 *)
Theorem guarded_productive : forall (k : Q) (b : nat) (c : Q),
  Id (gbottom_at b (grun k b c)) true.
Proof.
intros k b c. apply gbottom_true_of_budget0. apply guarded_ledger_clears.
Qed.

(* 健全性：q_decay_breaks 的击穿预算即守恒链的合格停时——
   链在该深度触底，且触底值（保持制冻结值）严格低于阈值 eps *)
Theorem guarded_breaks : forall (k c0 eps : Q),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => And (NatLe 1 N)
           (And (Id (gbottom_at N (grun k N c0)) true)
                (QltT (ghead_at N (grun k N c0)) eps))).
Proof.
intros k c0 eps Hk0 Hk1 Hc0 He.
destruct (q_decay_breaks k c0 eps Hk0 Hk1 Hc0 He) as [N [HN1 HN]].
exists N. split.
- exact HN1.
- split.
  + apply guarded_productive.
  + pose proof (grun_head_at k N N c0 (NatLe_lift N N (Nat.le_refl N))) as Hh.
    rewrite (RealSetoid.Id_eq (ghead_at N (grun k N c0)) (gval k c0 N) Hh).
    exact (st_qltT_qid_l (gval k c0 N) (c0 * q_pow (1 - k) N) eps
             (gval_pow_QId k N c0) HN).
Qed.

(* ============================================================ *)
(* §3 件 3：最小停时可判定构造（Q 层单调谓词线性搜索）                *)
(*   跨阈谓词 P n = (c0·(1−κ)^n < eps)：Qlt_bool 判定、衰减单调。     *)
(*   stsearch 从种子上界 U 线性下扫，返回最小跨阈指数 N* 连同           *)
(*   (界内、已跨阈、逐前项未跨阈) 三联证书；失败分支携带全程未跨阈证。   *)
(* ============================================================ *)

(* 跨阈谓词（可执行） *)
Definition st_pred_decay (k c0 eps : Q) : nat -> bool :=
  fun n => Qlt_bool (c0 * q_pow (1 - k) n) eps.

(* 搜索结果（Set 层）：命中 = 最小指数三联证书；脱靶 = 全程未跨阈证 *)
Definition st_hit (P : nat -> bool) (U : nat) : Set :=
  sigT (fun N => And (NatLe N U)
           (And (Id (P N) true)
                (forall j : nat, NatLt j N -> Id (P j) false))).

Definition st_miss (P : nat -> bool) (U : nat) : Set :=
  forall j : nat, NatLe j U -> Id (P j) false.

Definition st_res (P : nat -> bool) (U : nat) : Set :=
  Or (st_hit P U) (st_miss P U).

(* 搜索步（须 Defined：stsearch 是可执行判定器，提取探针要用其本体） *)
Lemma stsearch_step_0 (P : nat -> bool) : st_res P 0%nat.
Proof.
destruct (P 0%nat) eqn:E0.
- apply inl. exists 0%nat. split.
  + apply NatLe_lift. apply Nat.le_refl.
  + split.
    * apply RealSetoid.eq_Id. exact E0.
    * intros j Hj. exfalso.
      pose proof (proj1 (Nat.ltb_lt j 0%nat) (RealSetoid.Id_eq _ _ Hj)) as Hlt.
      lia.
- apply inr. intros j Hj. apply NatLe_drop in Hj. destruct j as [| j'].
  + apply RealSetoid.eq_Id. exact E0.
  + exfalso. lia.
Defined.

Lemma stsearch_step_S (P : nat -> bool) (U : nat) (r : st_res P U)
  : st_res P (Datatypes.S U).
Proof.
destruct r as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  apply inl. exists N. split.
  + apply NatLe_lift. apply NatLe_drop in HNle. lia.
  + split; assumption.
- destruct (P (Datatypes.S U)) eqn:E.
  + apply inl. exists (Datatypes.S U). split.
    * apply NatLe_lift. apply Nat.le_refl.
    * split.
      -- apply RealSetoid.eq_Id. exact E.
      -- intros j Hj. apply miss. apply NatLe_lift.
         apply NatLe_drop in Hj. lia.
  + apply inr. intros j Hj. apply NatLe_drop in Hj.
    destruct (Nat.eq_dec j (Datatypes.S U)) as [Heq | Hne].
    * rewrite Heq. apply RealSetoid.eq_Id. exact E.
    * apply miss. apply NatLe_lift. lia.
Defined.

(* 线性搜索本体：从上界 U 下扫到 0，保最小命中 *)
Fixpoint stsearch (P : nat -> bool) (U : nat) : st_res P U :=
  match U as u return st_res P u with
  | O => stsearch_step_0 P
  | Datatypes.S U' => stsearch_step_S P U' (stsearch P U')
  end.

(* 非负幂：0 ≤ x ⟹ 0 ≤ x^n（Qmult_le_0_compat 归纳） *)
Lemma st_qpow_nonneg : forall (x : Q) (n : nat), Qle 0 x -> Qle 0 (q_pow x n).
Proof.
intros x n Hx. induction n as [| n IH].
- (* Qle 0 1：经 uc_znat_pos 1（Z.of_nat 1 # 1 ≡ 1 定义性归约） *)
  exact (uc_znat_pos 1%nat).
- change (q_pow x (Datatypes.S n)) with (x * q_pow x n).
  apply Qmult_le_0_compat.
  + exact Hx.
  + exact IH.
Qed.

(* 衰减单调（件 3b 引擎）：n ≤ m 且 n 处已跨阈 ⟹ m 处仍跨阈
   （0 ≤ 1−κ ≤ 1 ⟹ (1−κ)^m ≤ (1−κ)^n，q_pow 指数加法 + uc_pow_le_drop；
   需 c0 ≥ 0 保乘法单调前提 0 ≤ c0·(1−κ)^n） *)
Lemma st_decay_mono : forall (k c0 eps : Q) (n m : nat),
  QltT 0 k -> QltT k 1 -> Qle 0 c0 ->
  NatLe n m -> QltT (c0 * q_pow (1 - k) n) eps ->
  QltT (c0 * q_pow (1 - k) m) eps.
Proof.
intros k c0 eps n m Hk0 Hk1 Hc0 Hle Hn.
apply NatLe_drop in Hle.
pose proof (QltT_to_Qlt _ _ Hn) as Hn'.
pose proof (st_qle_of_ltT 0 k Hk0) as H0k.
assert (H1kle : Qle 0 (1 - k))
  by (apply Qlt_le_weak; exact (uc_lt_opp_shift k 1 (QltT_to_Qlt k 1 Hk1))).
assert (Hle01 : Qle (1 - k) 1) by (apply st_qle_one_minus; exact H0k).
(* 指数裂变：q_pow (1−k) m == q_pow (1−k) n · q_pow (1−k) (m−n) *)
assert (Hdec : c0 * q_pow (1 - k) m
               == (c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat).
{ assert (Hm : (n + (m - n))%nat = m) by lia.
  assert (T2 : q_pow (1 - k) (n + (m - n))%nat == q_pow (1 - k) m)
    by (rewrite Hm; apply Qeq_refl).
  assert (Hpow : q_pow (1 - k) m
                 == q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat).
  { exact (Qeq_trans (q_pow (1 - k) m) (q_pow (1 - k) (n + (m - n))%nat)
             (q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat)
             (Qeq_sym (q_pow (1 - k) (n + (m - n))%nat) (q_pow (1 - k) m) T2)
             (uc_pow_add (1 - k) n (m - n)%nat)). }
  rewrite Hpow.
  exact (Qeq_sym ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                 (c0 * (q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat))
                 (st_mult_assoc_qeq c0 (q_pow (1 - k) n)
                    (q_pow (1 - k) (m - n)%nat))). }
(* 差项 ≤ 1 ⟹ 系数乘法收缩 *)
assert (Hgap : Qle ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                   (c0 * q_pow (1 - k) n)).
{ apply (uc_qeq_le_r ((c0 * q_pow (1 - k) n) * 1%Q) (c0 * q_pow (1 - k) n)
          ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)).
  - apply Qmult_1_r.
  - apply (uc_qeq_le_r (1%Q * (c0 * q_pow (1 - k) n))
             ((c0 * q_pow (1 - k) n) * 1%Q)
             ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)).
    + apply Qmult_comm.
    + apply (uc_qeq_le_l
               (q_pow (1 - k) (m - n)%nat * (c0 * q_pow (1 - k) n))
               ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
               (1%Q * (c0 * q_pow (1 - k) n))).
      * apply Qmult_comm.
      * apply (Qmult_le_compat_r (q_pow (1 - k) (m - n)%nat) 1%Q
                 (c0 * q_pow (1 - k) n)).
        -- exact (uc_pow_le_drop (1 - k) 0%nat (m - n)%nat H1kle Hle01).
        -- apply Qmult_le_0_compat.
           ++ exact Hc0.
           ++ exact (st_qpow_nonneg (1 - k) n H1kle). }
apply Qlt_to_QltT.
apply (uc_qeq_lt_l ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                   (c0 * q_pow (1 - k) m) eps (Qeq_sym _ _ Hdec)).
apply (Qle_lt_trans ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                    (c0 * q_pow (1 - k) n) eps).
- exact Hgap.
- exact Hn'.
Qed.

(* 最小停时 N*：存在性 + 3a 最小性证书 + 3b 上界单调证书 *)
Theorem minimal_stoptime : forall (k c0 eps : Q) (U : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun N => And (NatLe N U)
           (And (QltT (c0 * q_pow (1 - k) N) eps)
                (And (forall j : nat, NatLt j N -> QleT' eps (c0 * q_pow (1 - k) j))
                     (forall j : nat, NatLe N j -> QltT (c0 * q_pow (1 - k) j) eps)))).
Proof.
intros k c0 eps U Hk0 Hk1 Hc0 He HU.
destruct (stsearch (st_pred_decay k c0 eps) U) as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  exists N. split.
  + exact HNle.
  + split.
    * exact hP.
    * split.
      -- (* 3a 最小性：逐前项未跨阈证书 ⟹ eps ≤ 前项值 *)
         intros j Hj. apply st_qlt_false_ge. exact (hmin j Hj).
      -- (* 3b 上界单调：衰减单调把跨阈从 N* 传到一切后继 *)
         intros j Hj.
         exact (st_decay_mono k c0 eps N j Hk0 Hk1
                  (Qlt_le_weak 0%Q c0 (QltT_to_Qlt 0%Q c0 Hc0)) Hj hP).
- exfalso.
  pose proof (miss U (NatLe_lift U U (Nat.le_refl U))) as Hf.
  pose proof (id_trans (id_sym HU) Hf) as Hcontra. inversion Hcontra.
Qed.

(* 搜索报告（vm_compute 友好：不打印函数证书） *)
Definition stsearch_report (P : nat -> bool) (U : nat) : nat * bool :=
  match stsearch P U with
  | inl h => (projT1 h, true)
  | inr _ => (U, false)
  end.

(* ============================================================ *)
(* §4 件 4：阈值策略双目标占优（离散形态，纯序代数）                   *)
(*   策略 = 停时指数 + 该处跨阈证书。目标 1 合并次数 = 停时；           *)
(*   目标 2 无效服务数 = st_waste（停时前已跨阈仍在服务的步数）。       *)
(*   N* 同时极小化两目标：占优 1 停时 ≤ 竞品；占优 2 竞品在 [N*,M)      *)
(*   全程跨阈 ⟹ 其无效服务 ≥ 整段差距 M − N*。                        *)
(* ============================================================ *)

(* 无效服务计数器：停时 N 之前已跨阈（P = true）的步数——跨阈后仍在服务即无效 *)
Fixpoint st_waste (P : nat -> bool) (N : nat) : nat :=
  match N with
  | O => 0%nat
  | Datatypes.S m => (st_waste P m + (if P m then 1 else 0))%nat
  end.

(* 最小者的无效服务恰为零（逐前项未跨阈证书逐层累加） *)
Lemma st_waste_zero : forall (P : nat -> bool) (N : nat),
  (forall j : nat, NatLt j N -> Id (P j) false) -> Id (st_waste P N) 0%nat.
Proof.
intros P N. induction N as [| N IH]; intros Hmin.
- reflexivity.
- change (st_waste P (Datatypes.S N))
    with (st_waste P N + (if P N then 1 else 0))%nat.
  rewrite (RealSetoid.Id_eq _ _
             (IH (fun j Hj => Hmin j (st_natlt_lift j (Datatypes.S N)
                       (Nat.lt_lt_succ_r j N (st_natlt_drop j N Hj)))))).
  rewrite (RealSetoid.Id_eq _ _
             (Hmin N (st_natlt_lift N (Datatypes.S N)
                        (Nat.lt_succ_diag_r N)))).
  reflexivity.
Qed.

(* 计数下界：[a, m) 全程跨阈 ⟹ 无效服务 ≥ m − a *)
Lemma st_waste_lower : forall (P : nat -> bool) (a m : nat),
  NatLe a m ->
  (forall j : nat, NatLe a j -> NatLt j m -> Id (P j) true) ->
  NatLe (m - a)%nat (st_waste P m).
Proof.
intros P a m. induction m as [| m IH]; intros Hle Hge.
- apply NatLe_lift.
  change (st_waste P 0%nat) with 0%nat.
  apply NatLe_drop in Hle. lia.
- apply NatLe_lift.
  change (st_waste P (Datatypes.S m))
    with (st_waste P m + (if P m then 1 else 0))%nat.
  destruct (Nat.leb a m) eqn:Ea.
  + assert (H1 : NatLe (m - a)%nat (st_waste P m)).
    { apply IH.
      - exact (NatLe_lift a m (proj1 (Nat.leb_le a m) Ea)).
      - intros j Hj1 Hj2. apply Hge.
        * exact Hj1.
        * exact (st_natlt_lift j (Datatypes.S m)
                   (Nat.lt_lt_succ_r j m (st_natlt_drop j m Hj2))). }
    apply NatLe_drop in H1. apply NatLe_drop in Hle.
    assert (Ham : (a <= m)%nat) by exact (proj1 (Nat.leb_le a m) Ea).
    assert (Hs : ((Datatypes.S m) - a)%nat = (Datatypes.S (m - a))%nat) by lia.
    rewrite Hs.
    assert (HPm : (P m)%bool = true).
    { apply RealSetoid.Id_eq. apply Hge.
      - exact (NatLe_lift a m (proj1 (Nat.leb_le a m) Ea)).
      - exact (st_natlt_lift m (Datatypes.S m) (Nat.lt_succ_diag_r m)). }
    rewrite HPm.
    change (if true then 1 else 0)%nat with 1%nat.
    lia.
  + apply Nat.leb_gt in Ea. apply NatLe_drop in Hle.
    assert (Hz : ((Datatypes.S m) - a)%nat = 0%nat) by lia.
    rewrite Hz.
    destruct (P m); lia.
Qed.

(* 证书可测策略类：停时 + 该处跨阈见证 *)
Record st_policy (P : nat -> bool) : Set := mk_policy {
  pol_stop : nat;
  pol_break : Id (P pol_stop) true
}.

Arguments pol_stop {P} _.
Arguments pol_break {P} _.
Arguments mk_policy {P} _ _.

(* 双目标占优（纯序代数形态）：对任意持证竞品，
   目标 1：N* ≤ M（合并次数不增）；
   目标 2：waste(Nstar) = 0 且 waste(M) ≥ M − Nstar（无效服务被压制） *)
Theorem st_dominance : forall (P : nat -> bool) (Nstar : nat) (q : st_policy P),
  (forall j : nat, NatLt j Nstar -> Id (P j) false) ->
  Id (P Nstar) true ->
  (forall n m : nat, NatLe n m -> Id (P n) true -> Id (P m) true) ->
  And (NatLe Nstar (pol_stop q))
      (And (Id (st_waste P Nstar) 0%nat)
           (NatLe ((pol_stop q - Nstar)%nat)
                  (st_waste P (pol_stop q)))).
Proof.
intros P Nstar q Hmin hN Hmono. destruct q as [M hM].
split.
- (* 占优 1：M < N* 与逐前项未跨阈证书矛盾 *)
  destruct (Nat.leb Nstar M) eqn:E.
  + exact (NatLe_lift Nstar M (proj1 (Nat.leb_le Nstar M) E)).
  + exfalso.
    pose proof (Hmin M (st_natlt_lift M Nstar
                   (proj1 (Nat.leb_gt Nstar M) E))) as Hf.
    pose proof (id_trans (id_sym hM) Hf) as Hcontra. inversion Hcontra.
- split.
  + exact (st_waste_zero P Nstar Hmin).
  + assert (Hle : NatLe Nstar M).
    { destruct (Nat.leb Nstar M) eqn:E2.
      - exact (NatLe_lift Nstar M (proj1 (Nat.leb_le Nstar M) E2)).
      - exfalso.
        pose proof (Hmin M (st_natlt_lift M Nstar
                       (proj1 (Nat.leb_gt Nstar M) E2))) as Hf.
        pose proof (id_trans (id_sym hM) Hf) as Hcontra. inversion Hcontra. }
    apply st_waste_lower.
    * exact Hle.
    * intros j Hj1 Hj2. exact (Hmono Nstar j Hj1 hN).
Qed.

(* 阈值策略占优的几何衰减实例化：把件 3 的最小停时喂给件 4 的抽象格 *)
Theorem st_thresh_dominance : forall (k c0 eps : Q) (U : nat)
                                     (q : st_policy (st_pred_decay k c0 eps)),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun Nstar =>
          And (NatLe Nstar (pol_stop q))
              (And (QltT (c0 * q_pow (1 - k) Nstar) eps)
                   (And (Id (st_waste (st_pred_decay k c0 eps) Nstar) 0%nat)
                        (NatLe ((pol_stop q - Nstar)%nat)
                               (st_waste (st_pred_decay k c0 eps) (pol_stop q)))))).
Proof.
intros k c0 eps U q Hk0 Hk1 Hc0 He HU.
assert (Hmono : forall n m : nat,
          NatLe n m -> Id (st_pred_decay k c0 eps n) true ->
          Id (st_pred_decay k c0 eps m) true).
{ intros n m Hle Hn.
  exact (st_decay_mono k c0 eps n m Hk0 Hk1
           (Qlt_le_weak 0%Q c0 (QltT_to_Qlt 0%Q c0 Hc0)) Hle Hn). }
destruct (stsearch (st_pred_decay k c0 eps) U) as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  exists N.
  destruct (st_dominance (st_pred_decay k c0 eps) N q hmin hP Hmono)
    as [Hd1 [Hd2 Hd3]].
  split.
  + exact Hd1.
  + split.
    * exact hP.
    * split.
      -- exact Hd2.
      -- exact Hd3.
- exfalso.
  pose proof (miss U (NatLe_lift U U (Nat.le_refl U))) as Hf.
  pose proof (id_trans (id_sym HU) Hf) as Hcontra. inversion Hcontra.
Qed.

(* ============================================================ *)
(* §5 件 5：反面对照——无预算见证的自指恒值链                          *)
(*   uloop：每步预算恒为 1、终值恒为 c 的自指链（CoFixpoint 守卫允许，   *)
(*   但无递减见证）。三重平凡性：预算永不归零、检测永不触底、停时不存在，  *)
(*   与件 2 的 GuardedChain（预算递减⟹必触底）构成分离。              *)
(* ============================================================ *)

CoFixpoint uloop (c : Q) : GChain := gstep 1%nat c (uloop c).

(* 平凡性 a：预算恒为 1（match 观察者强制 cofix 展开，预算永不清零） *)
Lemma unguarded_budget_const : forall (c : Q) (n : nat),
  Id (gbudget_at n (uloop c)) 1%nat.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (gbudget_at (Datatypes.S n) (uloop c)) with (gbudget_at n (uloop c)).
  exact IH.
Qed.

(* 平凡性 b：终值恒为 c（自指恒值，永无改进轨迹） *)
Lemma unguarded_head_const : forall (c : Q) (n : nat),
  Id (ghead_at n (uloop c)) c.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (ghead_at (Datatypes.S n) (uloop c)) with (ghead_at n (uloop c)).
  exact IH.
Qed.

(* 平凡性 c：任意深度检测均为未触底 *)
Lemma unguarded_never_bottoms : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) false.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (gbottom_at (Datatypes.S n) (uloop c)) with (gbottom_at n (uloop c)).
  exact IH.
Qed.

(* 反面定理：无见证恒值链的停时不存在（触底检测 true 直接矛盾） *)
Theorem unguarded_no_stoptime : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) true -> Empty_set.
Proof.
intros c n H.
pose proof (unguarded_never_bottoms c n) as Hf.
pose proof (id_trans (id_sym H) Hf) as Hcontra. inversion Hcontra.
Qed.

(* 分离定理：恒值链的账本永不触及清零口径，与 GuardedChain 账本对立 *)
Theorem unguarded_vs_guarded : forall (c : Q) (n : nat),
  Id (gbudget_at n (uloop c)) 0%nat -> Empty_set.
Proof.
intros c n H0.
pose proof (unguarded_budget_const c n) as H1.
pose proof (id_trans (id_sym H0) H1) as Hcontra. inversion Hcontra.
Qed.

(* 平凡性总装（三联观察） *)
Theorem unguarded_trivial : forall (c : Q) (n : nat),
  And (Id (gbudget_at n (uloop c)) 1%nat)
      (And (Id (gbottom_at n (uloop c)) false)
           (Id (ghead_at n (uloop c)) c)).
Proof.
intros c n. split.
- apply unguarded_budget_const.
- split.
  + apply unguarded_never_bottoms.
  + apply unguarded_head_const.
Qed.

(* ---- 件 5 vm_compute 自测 ---- *)
Eval vm_compute in gbottom_at 7 (uloop (1#10)).
Eval vm_compute in gbudget_at 7 (uloop (1#10)).

Lemma test_uloop_never : Id (gbottom_at 7 (uloop (1#10))) false.
Proof. vm_compute. reflexivity. Qed.

Lemma test_uloop_budget : Id (gbudget_at 7 (uloop (1#10))) 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §6 件 3/件 4 联合 vm_compute 自测（G3 样例输出源之二）              *)
(*   c0 = 4/5, κ = 1/2, eps = 1/10：跨阈谓词在 n = 4 首次为真         *)
(*   （4/5, 2/5, 1/5, 1/10, 1/20）；stsearch 自上界 5 报最小停时 4。   *)
(* ============================================================ *)

Definition stpred_demo : nat -> bool := st_pred_decay (1#2) (8#10) (1#10).

Eval vm_compute in (stpred_demo 0, stpred_demo 1, stpred_demo 2,
                    stpred_demo 3, stpred_demo 4, stpred_demo 5).
Eval vm_compute in stsearch_report stpred_demo 5.
Eval vm_compute in st_waste stpred_demo 6.

Lemma test_stsearch_min : Id (stsearch_report stpred_demo 5) (4%nat, true).
Proof. vm_compute. reflexivity. Qed.

Lemma test_waste_star : Id (st_waste stpred_demo 4) 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_waste_gap : Id (st_waste stpred_demo 6) 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 提取探针（G3：Obj.magic = 0）                                  *)
(*   提取停时判定器全链：谓词 / 搜索 / 报告 / 无效服务计数 / 幂核。      *)
(* ============================================================ *)

Set Warnings "-extraction-opaque-accessed".
Extraction "upstoptime.ml" st_pred_decay stsearch stsearch_report st_waste q_pow.

End StopTime.
