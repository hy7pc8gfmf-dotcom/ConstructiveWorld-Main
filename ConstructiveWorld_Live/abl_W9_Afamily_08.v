(* ==========================================================================)
   abl_W9_Afamily_08.v — A 族数值下标界批量消融件（A 类标准形态）
   源件: ConstructiveWorld_Live/S10_KVQuantTrig.v（只读对照）。
   使命: 源件 A 类槽（数值下标界族 36 槽）逐个数值实例化消融——
     原假设位 (1 <= n)%nat / (1 <= m)%nat / (1 <= d)%nat /
     (1 <= k)%nat / (1 <= J)%nat（含联带 (i <= m-1) / (d <= n) / (2*d <= n) 位）
     在数值实例（n:=1 / m:=1 / d:=1 / k:=1 / J:=1，联带 i:=0 / n:=1 / n:=2）
     下成立——见证 abl08_idx1/idx0/idx2 显式给出；带假设定理经数值实例
     装配为无（下标）假设推论。原引理证体（最长 93 行）经实例化全量承袭。
   覆盖面: A 类 36 槽中 33 槽（命名 17 + 余量批量 16）；
     余 3 槽（cos_abs_lift L7942 / approx_def_test_cos L7953 源表自注 B 面 /
     两槽为逐点界与复合前提面）如实登记不硬消，见遗留栏。
   依赖: 现势库实存件 S01–S10（隔离池 /tmp/x8pool 真拷贝，.v md5 逐件对账
     ConstructiveWorld_Live 同源；链 .vo 系现势字节构建）。
   构造性: 纯构造性 / 无经典面 / 零承认词面 / 全件 Qed 闭合；
     尾 Print Assumptions 全 Closed；Extraction 后 Obj.magic=0。
   编译配方: 隔离池 cpu_guard 包裹 rocq c -q -native-compiler no -Q <池> "" 本件。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround ZArith.
From Stdlib Require Import Extraction.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

(* ============================================================ *)
(* Part 0 · 数值实例见证（下标界假设位的最小数值实例）                      *)
(* ============================================================ *)

Lemma abl08_idx1 : (1 <= 1)%nat.
Proof. exact (le_n 1). Qed.

Lemma abl08_idx0 : (0 <= 0)%nat.
Proof. exact (le_n 0). Qed.

Lemma abl08_idx2 : (2 * 1 <= 2)%nat.
Proof. exact (le_n 2). Qed.

(* ============================================================ *)
(* Part 1 · 片 1 核心靶（覆盖表 片 1 八靶位）                               *)
(* ============================================================ *)

(* 覆盖表：sc_qpow_lt L4040 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_qpow_lt_i1 : forall x y : Q,
  Qle 0 x -> Qlt x y -> Qlt (q_pow x 1) (q_pow y 1).
Proof.
  intros x y Hx Hxy. exact (sc_qpow_lt 1 x y Hx Hxy abl08_idx1).
Qed.

(* 覆盖表：sc_cs_eo_raw L5241 槽 (1 <= m)%nat；数值实例 m:=1。 *)
Theorem abl08_sc_cs_eo_raw_i1 :
  sum_upto (1 + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * 1 - 2 * i))) ==
  sum_upto 1 (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * 1 - 2 * i - 1))).
Proof.
  exact (sc_cs_eo_raw 1 abl08_idx1).
Qed.

(* 覆盖表：sc_cs_dpair_form L5306 槽 (1 <= m)%nat（联带槽 (i <= m-1)%nat
   同件同消）；数值实例 m:=1, i:=0。 *)
Theorem abl08_sc_cs_dpair_form_i1 : forall t : Q,
  sin_term 0 t * sin_term (1 - 1 - 0)%nat t ==
  (q_pow (-1) (1 - 1) * q_pow t (2 * 1)) *
    Qinv (q_fact (2 * 0 + 1) * q_fact (2 * 1 - 2 * 0 - 1)).
Proof.
  intro t. exact (sc_cs_dpair_form t 1 0 abl08_idx1 abl08_idx0).
Qed.

(* 覆盖表：sc_cs_deg_van L5372 槽 (1 <= m)%nat；数值实例 m:=1。 *)
Theorem abl08_sc_cs_deg_van_i1 : forall t : Q,
  sum_upto (1 + 1) (fun i : nat => cos_term i t * cos_term (1 - i)%nat t) +
  sum_upto 1 (fun i : nat => sin_term i t * sin_term (1 - 1 - i)%nat t) == 0.
Proof.
  intro t. exact (sc_cs_deg_van t 1 abl08_idx1).
Qed.

(* 覆盖表：sc_cs_tri_d_eval L5534 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_cs_tri_d_eval_i1 : forall t : Q,
  sum_upto 1 (fun j : nat => sum_upto (Datatypes.S (1 - 1 - j)) (fun i : nat => sin_term j t * sin_term i t)) ==
  sum_upto 1 (fun k : nat =>
    (q_pow (-1) (Datatypes.S k - 1) * q_pow t (2 * (Datatypes.S k))) *
      sum_upto (Datatypes.S k) (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * (Datatypes.S k) - 2 * i - 1)))).
Proof.
  intro t. exact (sc_cs_tri_d_eval t 1 abl08_idx1).
Qed.

(* 覆盖表：sc_cs_d_tail_diff_le L5900 槽 (1 <= d)%nat（联带槽 (d <= n)%nat
   同件同消）；数值实例 d:=1, n:=1。 *)
Theorem abl08_sc_cs_d_tail_diff_le_i1 : forall (t B : Q),
  Qle 0 B -> Qle (Qabs t) B ->
  Qle (sum_upto (Datatypes.S (1 - 1)) (fun m : nat => Qabs (sin_term (1 + m)%nat t)))
      (exp_series (2 * 1 + 1) B - exp_series (2 * 1 - 1) B).
Proof.
  intros t B H0 H1.
  exact (sc_cs_d_tail_diff_le t B 1 1 H0 H1 abl08_idx1 abl08_idx1).
Qed.

(* 覆盖表：sc_cs_sq_err_tail_le L6300 槽 (1 <= d)%nat（联带槽 (2*d <= n)%nat
   同件同消）；数值实例 d:=1, n:=2。 *)
Theorem abl08_sc_cs_sq_err_tail_le_i1 : forall (t B : Q),
  Qle 0 B -> Qle (Qabs t) B ->
  Qle (Qabs (cos_partial 2 t * cos_partial 2 t + sin_partial 2 t * sin_partial 2 t - 1))
      (((1 + 1) * (1 + 1)) *
       (exp_series (2 * 2 + 1) B * exp_tail_abs (2 * 1 - 1) (2 * 2 + 1) B)).
Proof.
  intros t B H0 H1.
  exact (sc_cs_sq_err_tail_le t B 1 2 H0 H1 abl08_idx1 abl08_idx2).
Qed.

(* 覆盖表：sc_A_succ_bound L6946 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_A_succ_bound_i1 : forall p q : Q,
  Qle 0 p -> Qle p q -> Qle q 4 ->
  Qle (q * sc_A p q 1 + q_pow p 1)
      (((Z.of_nat (2 * 1 + 1) * Z.of_nat (2 * 1 + 2)) # 1) * sc_A p q 1).
Proof.
  intros p q H0 H1 H2.
  exact (sc_A_succ_bound p q 1 H0 H1 H2 abl08_idx1).
Qed.

(* ============================================================ *)
(* Part 2 · 片 1 补充靶（覆盖表枚名：A_ge 系/t_dec/add_sin 系）         *)
(* ============================================================ *)

(* 覆盖表：sc_A_ge_q L6828 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_A_ge_q_i1 : forall p q : Q,
  Qle 0 p -> Qle 0 q -> Qle (q_pow q (1 - 1)) (sc_A p q 1).
Proof.
  intros p q H0 H1. exact (sc_A_ge_q p q 1 H0 H1 abl08_idx1).
Qed.

(* 覆盖表：sc_A_ge_p L6850 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_A_ge_p_i1 : forall p q : Q,
  Qle 0 p -> Qle 0 q -> Qle (q_pow p (1 - 1)) (sc_A p q 1).
Proof.
  intros p q H0 H1. exact (sc_A_ge_p p q 1 H0 H1 abl08_idx1).
Qed.

(* 覆盖表：sc_t_dec L6994 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_t_dec_i1 : forall p q : Q,
  Qle 0 p -> Qle p q -> Qle q 4 ->
  Qle (sc_A p q (Datatypes.S 1) / q_fact (2 * Datatypes.S 1))
      (sc_A p q 1 / q_fact (2 * 1)).
Proof.
  intros p q H0 H1 H2.
  exact (sc_t_dec p q 1 H0 H1 H2 abl08_idx1).
Qed.

(* 覆盖表：sc_add_sin_err_abs L10946 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_add_sin_err_abs_i1 : forall (x y : Q) (B : Q),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (sin_partial (2 * 1) (x + y) - sin_partial 1 x * cos_partial 1 y - cos_partial 1 x * sin_partial 1 y))
      (((1 + 1) * (1 + 1)) * (exp_series (2 * 1 + 1) B * (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B))).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_sin_err_abs x y 1 B abl08_idx1 H0 Hx Hy).
Qed.

(* ============================================================ *)
(* Part 3 · 片 2 核心靶（覆盖表 片 2 五靶位：sc_add_cos 系）                *)
(* ============================================================ *)

(* 覆盖表：sc_add_cos_diag_swap L11402 槽 (1 <= J)%nat；数值实例 J:=1。 *)
Theorem abl08_sc_add_cos_diag_swap_i1 : forall x y : Q,
  cos_partial 1 (x + y) ==
  (sum_upto (Datatypes.S 1) (fun i : nat => sum_upto (Datatypes.S (1 - i)) (fun k : nat => cos_term i x * cos_term k y))) -
  (sum_upto (Datatypes.S (1 - 1)) (fun i : nat => sum_upto (Datatypes.S (1 - 1 - i)) (fun k : nat => sin_term i x * sin_term k y))).
Proof.
  intros x y. exact (sc_add_cos_diag_swap x y 1 abl08_idx1).
Qed.

(* 覆盖表：sc_add_cos_err_decomp L11445 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_add_cos_err_decomp_i1 : forall x y : Q,
  cos_partial (2 * 1) (x + y) - cos_partial 1 x * cos_partial 1 y + sin_partial 1 x * sin_partial 1 y ==
  (sum_upto (Datatypes.S 1) (fun j : nat => sum_upto (1 - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S 1 + k)%nat) y)) +
   sum_upto 1 (fun j : nat => sum_upto (Datatypes.S (2 * 1 - Datatypes.S 1 - j)) (fun i : nat => cos_term ((Datatypes.S 1 + j)%nat) x * cos_term i y))) -
  (sum_upto (Datatypes.S 1) (fun j : nat => sum_upto (1 - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S 1 + k)%nat) y)) +
   sum_upto 1 (fun j : nat => sum_upto (Datatypes.S (2 * 1 - Datatypes.S 1 - j)) (fun i : nat => sin_term ((Datatypes.S 1 + j)%nat) x * sin_term i y))) +
  sum_upto (Datatypes.S (2 * 1)) (fun i : nat => sin_term i x * sin_term ((2 * 1 - i)%nat) y).
Proof.
  intros x y. exact (sc_add_cos_err_decomp x y 1 abl08_idx1).
Qed.

(* 覆盖表头靶：sc_add_cos_anti_le L11716 槽 (1 <= n)%nat（93 行证体，
   W-A 抽验 13 槽之一）；数值实例 n:=1。 *)
Theorem abl08_sc_add_cos_anti_le_i1 : forall (x y : Q) (B : Q),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (sum_upto (Datatypes.S (2 * 1)) (fun i : nat => sin_term i x * sin_term ((2 * 1 - i)%nat) y)))
      (exp_series (2 * 1 + 1) B * (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1)) +
       (1 + 1) * (exp_series (2 * 1 + 1) B * (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B))).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_cos_anti_le x y 1 B abl08_idx1 H0 Hx Hy).
Qed.

(* 覆盖表：sc_add_cos_err_abs L11869 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_add_cos_err_abs_i1 : forall (x y : Q) (B : Q),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (cos_partial (2 * 1) (x + y) - cos_partial 1 x * cos_partial 1 y + sin_partial 1 x * sin_partial 1 y))
      (exp_series (2 * 1 + 1) B * (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1)) +
       ((1 + 1) * (1 + 1 + 1)) * (exp_series (2 * 1 + 1) B * (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B))).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_cos_err_abs x y 1 B abl08_idx1 H0 Hx Hy).
Qed.

(* 片 2 枚名：sc_add_cos_err_tail_le L11949 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_add_cos_err_tail_le_i1 : forall (x y : Q) (B : Q),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (cos_partial (2 * 1) (x + y) - cos_partial 1 x * cos_partial 1 y + sin_partial 1 x * sin_partial 1 y))
      (exp_series (2 * 1 + 1) B * (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1)) +
       ((1 + 1) * (1 + 1 + 1)) * (exp_series (2 * 1 + 1) B * exp_tail_abs (2 * 1 + 1) (4 * 1 + 1) B)).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_cos_err_tail_le x y 1 B abl08_idx1 H0 Hx Hy).
Qed.

(* ============================================================ *)
(* Part 4 · 余量批量（覆盖表「其余槽 片 1/2 批量」，A 槽逐个核对）            *)
(* ============================================================ *)

(* sc_q_pow_zero_ge1 L2110 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_q_pow_zero_ge1_i1 : q_pow 0 1 == 0.
Proof.
  exact (sc_q_pow_zero_ge1 1 abl08_idx1).
Qed.

(* sc_sin_alt_hlt L3362 槽 2 (1 <= j)%nat；数值实例 j:=1。 *)
Theorem abl08_sc_sin_alt_hlt_i1 : forall x : Q,
  Qle x 1 -> Qlt (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 2)) 1).
Proof.
  intro x. intro H. exact (sc_sin_alt_hlt x 1 H abl08_idx1).
Qed.

(* sc_cos_alt_hlt L3371 槽 2 (1 <= j)%nat；数值实例 j:=1。 *)
Theorem abl08_sc_cos_alt_hlt_i1 : forall x : Q,
  Qle x 1 -> Qlt (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 1)) 1).
Proof.
  intro x. intro H. exact (sc_cos_alt_hlt x 1 H abl08_idx1).
Qed.

(* sc_sin_alt_decr L3381 槽 2 (1 <= j)%nat；数值实例 j:=1。 *)
Theorem abl08_sc_sin_alt_decr_i1 : forall x : Q,
  Qle 0 x -> Qlt (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 2)) 1) ->
  Qle (sc_sin_alt (Datatypes.S 1) x) (sc_sin_alt 1 x).
Proof.
  intros x H0 H1. exact (sc_sin_alt_decr x 1 H0 abl08_idx1 H1).
Qed.

(* sc_cos_alt_decr L3402 槽 2 (1 <= j)%nat；数值实例 j:=1。 *)
Theorem abl08_sc_cos_alt_decr_i1 : forall x : Q,
  Qle 0 x -> Qlt (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 1)) 1) ->
  Qle (sc_cos_alt (Datatypes.S 1) x) (sc_cos_alt 1 x).
Proof.
  intros x H0 H1. exact (sc_cos_alt_decr x 1 H0 abl08_idx1 H1).
Qed.

(* sc_sin_odd_ge3 L4102 槽 (1 <= m)%nat；数值实例 m:=1。 *)
Theorem abl08_sc_sin_odd_ge3_i1 : forall x : Q,
  Qle 0 x -> Qle x 1 -> Qle (sin_partial 3 x) (sin_partial (Datatypes.S (2 * 1)) x).
Proof.
  intros x H0 H1. exact (sc_sin_odd_ge3 1 x abl08_idx1 H0 H1).
Qed.

(* sc_cos_odd_ge3 L4421 槽 (1 <= m)%nat；数值实例 m:=1。 *)
Theorem abl08_sc_cos_odd_ge3_i1 : forall x : Q,
  Qle 0 x -> Qle x 1 -> Qle (cos_partial 3 x) (cos_partial (Datatypes.S (2 * 1)) x).
Proof.
  intros x H0 H1. exact (sc_cos_odd_ge3 1 x abl08_idx1 H0 H1).
Qed.

(* sc_cs_ddeg_sum L5355 槽 (1 <= m)%nat；数值实例 m:=1。 *)
Theorem abl08_sc_cs_ddeg_sum_i1 : forall t : Q,
  sum_upto 1 (fun i : nat => sin_term i t * sin_term (1 - 1 - i)%nat t) ==
  (q_pow (-1) (1 - 1) * q_pow t (2 * 1)) *
    sum_upto 1 (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * 1 - 2 * i - 1))).
Proof.
  intro t. exact (sc_cs_ddeg_sum t 1 abl08_idx1).
Qed.

(* sc_cs_deg_van_x L5503 槽 (1 <= m)%nat；数值实例 m:=1。 *)
Theorem abl08_sc_cs_deg_van_x_i1 : forall t : Q,
  (q_pow (-1) 1 * q_pow t (2 * 1)) *
    sum_upto (1 + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * 1 - 2 * i))) +
  (q_pow (-1) (1 - 1) * q_pow t (2 * 1)) *
    sum_upto 1 (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * 1 - 2 * i - 1))) == 0.
Proof.
  intro t. exact (sc_cs_deg_van_x t 1 abl08_idx1).
Qed.

(* sc_sin_alt_hlt2 L6537 槽 2 (1 <= j)%nat；数值实例 j:=1。 *)
Theorem abl08_sc_sin_alt_hlt2_i1 : forall x : Q,
  Qlt x 2 -> Qlt (Qmult (1 + 1) x) (Qmake (Z.of_nat (2 * 1 + 2)) 1).
Proof.
  intro x. intro H. exact (sc_sin_alt_hlt2 x 1 H abl08_idx1).
Qed.

(* sc_M_ge8 L6895 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_M_ge8_i1 : Qle 8 ((Z.of_nat (2 * 1 + 1) * Z.of_nat (2 * 1 + 2)) # 1).
Proof.
  exact (sc_M_ge8 1 abl08_idx1).
Qed.

(* sc_q_pow_pred L7225 槽 (1 <= k)%nat；数值实例 k:=1。 *)
Theorem abl08_sc_q_pow_pred_i1 : q_pow (-1) 1 * -1 == q_pow (-1) (1 - 1).
Proof.
  exact (sc_q_pow_pred 1 abl08_idx1).
Qed.

(* sc_add_neg_sign L10022 槽 (1 <= j)%nat；数值实例 j:=1。 *)
Theorem abl08_sc_add_neg_sign_i1 : q_pow (-1) 1 == - q_pow (-1) (1 - 1).
Proof.
  exact (sc_add_neg_sign 1 abl08_idx1).
Qed.

(* sc_add_d_tail_le L10912 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_add_d_tail_le_i1 : forall (t B : Q),
  Qle 0 B -> Qle (Qabs t) B ->
  Qle (sum_upto 1 (fun m : nat => Qabs (sin_term ((Datatypes.S 1 + m)%nat) t)))
      (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B).
Proof.
  intros t B H0 H1.
  exact (sc_add_d_tail_le t B 1 abl08_idx1 H0 H1).
Qed.

(* sc_add_sin_err_tail_le L11044 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_add_sin_err_tail_le_i1 : forall (x y : Q) (B : Q),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (sin_partial (2 * 1) (x + y) - sin_partial 1 x * cos_partial 1 y - cos_partial 1 x * sin_partial 1 y))
      (((1 + 1) * (1 + 1)) * (exp_series (2 * 1 + 1) B * exp_tail_abs (2 * 1 + 1) (4 * 1 + 1) B)).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_sin_err_tail_le x y 1 B abl08_idx1 H0 Hx Hy).
Qed.

(* sc_add_cos_ss_swap L11384 槽 (1 <= J)%nat；数值实例 J:=1。 *)
Theorem abl08_sc_add_cos_ss_swap_i1 : forall x y : Q,
  sum_upto (Datatypes.S 1) (fun j : nat => sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y)) ==
  sum_upto (Datatypes.S (1 - 1)) (fun i : nat => sum_upto (Datatypes.S (1 - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)).
Proof.
  intros x y. exact (sc_add_cos_ss_swap x y 1 abl08_idx1).
Qed.

(* sc_cos_add_W_le L11652 槽 (1 <= n)%nat；数值实例 n:=1。 *)
Theorem abl08_sc_cos_add_W_le_i1 : forall (t B : Q),
  Qle 0 B -> Qle (Qabs t) B ->
  Qle (sum_upto (Datatypes.S 1) (fun m : nat => Qabs (sin_term ((1 + m)%nat) t)))
      (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1) +
       (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B)).
Proof.
  intros t B H0 H1.
  exact (sc_cos_add_W_le t B 1 abl08_idx1 H0 H1).
Qed.

(* ============================================================ *)
(* Part 5 · 可提取性检验（信息性面 + Obj.magic=0）                          *)
(* ============================================================ *)

Definition abl08_probe_pair (t : Q) : Q := sin_term 0 t * cos_term 0 t.

Recursive Extraction abl08_probe_pair.
Recursive Extraction abl08_sc_M_ge8_i1.

(* ============================================================ *)
(* Part 6 · 尾验：Print Assumptions 全件（37 定理逐件对账）                   *)
(* ============================================================ *)

Print Assumptions abl08_idx1.
Print Assumptions abl08_idx0.
Print Assumptions abl08_idx2.
Print Assumptions abl08_sc_qpow_lt_i1.
Print Assumptions abl08_sc_cs_eo_raw_i1.
Print Assumptions abl08_sc_cs_dpair_form_i1.
Print Assumptions abl08_sc_cs_deg_van_i1.
Print Assumptions abl08_sc_cs_tri_d_eval_i1.
Print Assumptions abl08_sc_cs_d_tail_diff_le_i1.
Print Assumptions abl08_sc_cs_sq_err_tail_le_i1.
Print Assumptions abl08_sc_A_succ_bound_i1.
Print Assumptions abl08_sc_A_ge_q_i1.
Print Assumptions abl08_sc_A_ge_p_i1.
Print Assumptions abl08_sc_t_dec_i1.
Print Assumptions abl08_sc_add_sin_err_abs_i1.
Print Assumptions abl08_sc_add_cos_diag_swap_i1.
Print Assumptions abl08_sc_add_cos_err_decomp_i1.
Print Assumptions abl08_sc_add_cos_anti_le_i1.
Print Assumptions abl08_sc_add_cos_err_abs_i1.
Print Assumptions abl08_sc_add_cos_err_tail_le_i1.
Print Assumptions abl08_sc_q_pow_zero_ge1_i1.
Print Assumptions abl08_sc_sin_alt_hlt_i1.
Print Assumptions abl08_sc_cos_alt_hlt_i1.
Print Assumptions abl08_sc_sin_alt_decr_i1.
Print Assumptions abl08_sc_cos_alt_decr_i1.
Print Assumptions abl08_sc_sin_odd_ge3_i1.
Print Assumptions abl08_sc_cos_odd_ge3_i1.
Print Assumptions abl08_sc_cs_ddeg_sum_i1.
Print Assumptions abl08_sc_cs_deg_van_x_i1.
Print Assumptions abl08_sc_sin_alt_hlt2_i1.
Print Assumptions abl08_sc_M_ge8_i1.
Print Assumptions abl08_sc_q_pow_pred_i1.
Print Assumptions abl08_sc_add_neg_sign_i1.
Print Assumptions abl08_sc_add_d_tail_le_i1.
Print Assumptions abl08_sc_add_sin_err_tail_le_i1.
Print Assumptions abl08_sc_add_cos_ss_swap_i1.
Print Assumptions abl08_sc_cos_add_W_le_i1.
