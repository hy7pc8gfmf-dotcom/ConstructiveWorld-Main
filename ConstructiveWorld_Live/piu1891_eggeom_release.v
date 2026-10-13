(* 五字段指针｜模块：piu1891_eggeom_release.v。
   数学使命：cos_pi_half（π/2 的内层零点，区间 (3/2, 5/3)）与 5/3 之间
   分离常数的显式字面见证——一致界常数取字面 C := 8、半比窗级取字面
   N := 10，分离常数 eps := (1/400)/8 = 1/3200；并经常数乘 2 提升至
   real_pi_geom 与 10/3 的分离形（LW0LeibSeparation leibsep_q_kernel
   的 eg 前提位所需形）。语句面四层：字面级数一致界（B=2、C=8）→
   Q 层逐点形（cos_zero_seq 面）→ cos 层 real_lt 包装 →
   real_pi_geom 层 real_lt 形。
   依赖：Stdlib QArith/Qabs/Qminmax/Lia/ZArith/Arith/Lqa/Setoid；
   S01_BaseRing（NatLe/NatLe_drop）；S02_CauchyComplete（QltT/real_lt/
   Qlt_to_QltT/Qle_to_QleT'/QleT'_to_Qle）；S03_QExp（exp_series/
   q_pow/q_fact/exp_series_mono/exp_series_tail_le/exp_tail_abs_geom2）；
   S07_RealSetoidExpLog（log_eps/log_eps_lt_delta/real_lt_mult_compat/
   real_const_lt）；S10_KVQuantTrig（cos_zero_seq/cos_pi_half/
   real_pi_geom/sc_cos_zero_upper_margin_gen/cos_root_pt_bound/
   cos_zero_upper/cos_zero_abs_le_two/cos_pi_half_proj）。
   对标行：S10_KVQuantTrig :9302 real_lt_cos_pi_half_five_thirds
   （其 eps = (1/400)/C 的 C 与窗级 N 均为存在消解见证——本件以
   exp_tail_abs_geom2 显式尾界与 log_eps 闭式将两者取为字面 8 与 9）；
   S10 :9372 real_pi_geom_lt_ten_thirds（提升链逐字同源）。
   构造性：零公理/零承认式/零经典逻辑；一致界由 exp_tail_abs_geom2
   显式尾和引理给出（无新增归纳）；Q 面显式链（Qlt_trans/Qlt_minus_iff/
   Qlt_shift_div_l/q_neq_of_lt）；闭 Q 值叶 vm_compute；nat 面 lia
   限辅助步。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <vo>/Local ""
   -Q <vo> ""（cwd 本件沙箱；cpu_guard v3 包裹）。命名：piu1891_ 前缀。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith Lqa Setoid.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.

(* ---------- §1 字面级数一致界：B=2 的部分和 ≤ 8 ----------
   exp_series mm 2 = Σ_{k≤mm} 2^k/k!；mm ≥ 5 时由尾和引理
   exp_tail_abs_geom2（A:=2、m:=5）得尾和 ≤ (2^5/5!)·2 = 8/15，
   而 exp_series 5 2 = 109/15，合计 39/5 ≤ 8；mm < 5 时单调性。 *)

Lemma piu1891_exp2_tail_cond : forall t : nat, (5 <= t)%nat ->
  QleT' ((1 + 1)%Q * 2%Q) ((Z.of_nat (t + 1) # 1)%Q).
Proof.
  intros t Ht.
  apply Qle_to_QleT'.
  change (Qle (4 # 1) ((Z.of_nat (t + 1) # 1)%Q)).
  assert (Hz : (4 <= Z.of_nat (t + 1))%Z) by (apply Z2Nat.inj_le; lia).
  unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Theorem piu1891_exp_series2_le8 : forall mm : nat,
  QleT' (exp_series mm 2) (8 # 1)%Q.
Proof.
  intros mm.
  apply Qle_to_QleT'.
  assert (H02 : Qle 0 2) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hcond : forall t : nat, (5 <= t)%nat ->
           Qle ((1 + 1)%Q * 2%Q) ((Z.of_nat (t + 1) # 1)%Q))
    by (intros t Ht; apply (QleT'_to_Qle _ _); apply piu1891_exp2_tail_cond; exact Ht).
  destruct (Nat.leb 5 mm) eqn:E.
  - apply Nat.leb_le in E.
    assert (Hd : Qle (exp_series mm 2 - exp_series 5 2)
                     ((q_pow 2 5 / q_fact 5) * (1 + 1))%Q).
    { apply (Qle_trans _ (exp_tail_abs 5 mm 2)).
      - apply (exp_series_tail_le 2 5 mm H02 E).
      - apply (exp_tail_abs_geom2 2 5 mm H02 Hcond E). }
    apply (Qle_trans _ (exp_series 5 2 + (q_pow 2 5 / q_fact 5) * (1 + 1))%Q).
    + apply (proj2 (Qle_minus_iff (exp_series mm 2)
                    (exp_series 5 2 + (q_pow 2 5 / q_fact 5) * (1 + 1))%Q)).
      setoid_replace (exp_series 5 2 + (q_pow 2 5 / q_fact 5) * (1 + 1)
                      + -(exp_series mm 2))
        with ((q_pow 2 5 / q_fact 5) * (1 + 1)
              - (exp_series mm 2 - exp_series 5 2)) by ring.
      apply (proj1 (Qle_minus_iff (exp_series mm 2 - exp_series 5 2)
                                  ((q_pow 2 5 / q_fact 5) * (1 + 1)))).
      exact Hd.
    + vm_compute. discriminate.
  - apply Nat.leb_gt in E.
    apply (Qle_trans _ (exp_series 5 2)).
    + apply (exp_series_mono 2 mm 5 H02). lia.
    + vm_compute. discriminate.
Qed.

(* ---------- §2 Q 层逐点形：cos_zero_seq n < 5/3 − 1/3200（n ≥ 10） ----------
   半比衰减 log_eps n = (1/2)^(S n) 取字面 t := 9（(1/2)^9 = 1/512 <
   1/400），margin 引理以字面 C := 8 实例化，分离常数 (1/400)/8 = 1/3200。 *)

Theorem piu1891_egcos_lit : forall n : nat, NatLe 10 n ->
  QltT (1 # 3200)%Q ((5 # 3)%Q - cos_zero_seq n)%Q.
Proof.
  assert (HC1 : QleT' 1 (8 # 1)%Q)
    by (apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia).
  assert (HC : forall mm : nat, QleT' (exp_series mm 2) (8 # 1)%Q)
    by (intros mm; apply piu1891_exp_series2_le8).
  assert (Ht : Qlt (1 * q_pow (1 / 2)%Q 9) (1 / 400))
    by (vm_compute; reflexivity).
  intros n Hn.
  assert (Hlog : Qlt (log_eps n) (1 / 400)).
  { apply (log_eps_lt_delta (1 / 400) 9 n).
    - exact Ht.
    - apply NatLe_drop. exact Hn. }
  destruct (cos_root_pt_bound n) as [N1 HN1].
  set (k := Nat.max 4 N1).
  assert (Hk4 : (4 <= k)%nat) by (unfold k; apply Nat.le_max_l).
  assert (HkN1 : (N1 <= k)%nat) by (unfold k; apply Nat.le_max_r).
  assert (Hroot : Qlt (Qabs (cos_partial k (cos_zero_seq n) - 0)) (log_eps n))
    by (apply (HN1 k HkN1)).
  assert (Hz53 : Qlt (cos_zero_seq n) (5 / 3)) by (apply cos_zero_upper).
  assert (HzT : QleT' (Qabs (cos_zero_seq n)) 2)
    by (apply Qle_to_QleT'; apply cos_zero_abs_le_two).
  assert (Hmgn : Qlt ((3 / 400) / (8 # 1)%Q) (5 / 3 - cos_zero_seq n)).
  { apply (sc_cos_zero_upper_margin_gen (8 # 1)%Q n k (cos_zero_seq n)
           Hk4 HC1 HC Hlog HzT Hroot Hz53). }
  assert (Heps : Qlt (1 # 3200)%Q ((3 # 400)%Q / (8 # 1)%Q))
    by (vm_compute; reflexivity).
  assert (Hfinal : Qlt (1 # 3200)%Q (5 / 3 - cos_zero_seq n)).
  { apply (Qlt_trans _ ((3 # 400)%Q / (8 # 1)%Q)).
    - exact Heps.
    - exact Hmgn. }
  apply Qlt_to_QltT.
  exact Hfinal.
Qed.

(* ---------- §3 Real 层包装与 real_pi_geom 提升形 ----------
   real_lt 包装取字面 eps = 1/3200 与字面窗级 10；提升链与
   S10 real_pi_geom_lt_ten_thirds 逐字同源（real_lt_mult_compat
   以常数 real_const 2 乘，配 2·(5/3) == 10/3 的逐点等式）。 *)

Theorem piu1891_coshalf_lit : real_lt cos_pi_half (real_const (5 / 3)).
Proof.
  unfold real_lt.
  exists (1 # 3200)%Q.
  split.
  - apply Qlt_to_QltT. vm_compute. reflexivity.
  - exists 10%nat.
    intros n Hn.
    apply Qlt_to_QltT.
    setoid_replace (projT1 (real_const (5 / 3)) n - projT1 cos_pi_half n)
      with (5 / 3 - cos_zero_seq n).
    + apply (QltT_to_Qlt _ _). exact (piu1891_egcos_lit n Hn).
    + apply Qeq_sym.
      assert (Hp : projT1 cos_pi_half n == cos_zero_seq n)
        by (apply cos_pi_half_proj).
      assert (Hc : projT1 (real_const (5 / 3)) n == 5 / 3)
        by (apply real_const_proj).
      rewrite Hc. rewrite Hp. reflexivity.
Qed.

Theorem piu1891_eggeom_lit : real_lt real_pi_geom (real_const (10 / 3)).
Proof.
  unfold real_pi_geom.
  apply (real_lt_eq_lt _ (real_mult (real_const 2) (real_const (5 / 3))) _).
  - apply (real_lt_mult_compat cos_pi_half (real_const (5 / 3)) (real_const 2)).
    + apply real_const_lt. change (Qlt 0 2). compute. reflexivity.
    + exact piu1891_coshalf_lit.
  - apply real_eq_of_zero_diff. intro n.
    rewrite (real_mult_proj (real_const 2) (real_const (5 / 3)) n).
    rewrite (real_const_proj 2 n). rewrite (real_const_proj (5 / 3) n).
    rewrite (real_const_proj (10 / 3) n). field.
Qed.

(* ========== 编译出口核对 ========== *)

Check piu1891_exp2_tail_cond.
Check piu1891_exp_series2_le8.
Check piu1891_egcos_lit.
Check piu1891_coshalf_lit.
Check piu1891_eggeom_lit.

Print Assumptions piu1891_exp2_tail_cond.
Print Assumptions piu1891_exp_series2_le8.
Print Assumptions piu1891_egcos_lit.
Print Assumptions piu1891_coshalf_lit.
Print Assumptions piu1891_eggeom_lit.
