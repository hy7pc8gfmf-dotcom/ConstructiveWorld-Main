(* 五字段指针｜模块：piu1879_gaplit_release.v。
   数学使命：gap 证书字面释放
   ＋cert 承载位接合肢：
   ①e3 字面释放（1/100·N=3）——kernel LW0LeibSeparation :5461 使用的
     real_pi_leibniz_gt_three（S10 :3043·证明体已钉同字面）存在形在
     lw0m_xL 面逐点形显形；
   ②el 字面释放（1/60·N=2）——kernel :5460 使用的
     real_pi_leibniz_lt_ten_thirds（S10 :8807·证明体已钉同字面）显形；
   ③cert 承载位接合肢：4/((h+1)·q_fact(40h+48)) ≤ 1/60——1872 装配 §8
     Hcert_eg/Hcert_el 参数位形（piu1872_bridge 除法自由链）；1/60 < 1/100
     故同一肢覆盖双参数位。eg_geom（real_pi_geom_lt_ten_thirds·eps=(1/400)/C
     系 exp_series_arch 见证字面未确定）释放不在本件（显式分档：该肢较深，
     留待后续模块承担）。
   结构注记：S10 释放工艺内件 lp_four/lp_odd/lp_a/
   sc_lp_* 五件公开可达；lw0m_xL :20 定义性＝lp_four·lp_odd；
   piu1864_two_nsel_height : 2·nsel+2 = 40h+48 换算已建立；
   κ₀/κ₁ 交错和 max-项主导）。
   本件之外：阀 Q 算术链（piu1880_valve_qchain）、
   κ₀/κ₁ 交错和界、carrier 内链重构，均不在本件。
   依赖：Stdlib QArith/Qabs/ZArith/Arith/Lia/Setoid；S01_BaseRing
   （NatLe/NatLe_drop）；S02_CauchyComplete（QltT/Qlt_to_QltT）；
   S03_QExp（q_fact/q_fact_pos）；S10_KVQuantTrig（lp_four/lp_odd/
   lp_a/sc_lp_three_margin/sc_lp_odd_chain/sc_lp_four_nonneg/
   sc_lp_six_margin/sc_lp_odd_le_s6）；LW0MLicBridge（lw0m_xL）；
   leibsep_band_ck_assembly（piu1872_bridge/piu1872_qfact_mono·
   1872 编译世界 -Q 引用·只读）。对标：mathlib/stdlib 无直接对应；字面沿用 S10 real_pi_leibniz_* 原字面。
   构造性：零公理/零承认式/零经典逻辑；e3/el 字面＝S10 原钉字面
   （语句外零字面预告）；Q 面线性收尾显式链（Qlt_le_trans/
   Qplus_le_compat/Qopp_le_compat/Qmult_le_compat_r/sc_lp_*）；
   nat 面 lia；闭 Q 值叶 vm_compute（1868 :162 同款配方）。
   编译配方：coqc -native-compiler no -q -Q . "" -Q <vo>/Local ""
   -Q <vo> "" -Q <1872world> ""（cwd 本件沙箱；cpu_guard v3 包裹）。
   命名：piu1879_ 前缀。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Arith.Arith Lqa Setoid.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import LW0MLicBridge.
Require Import leibsep_band_ck_assembly.

(* ---------- §1 e3 字面释放（1/100·N=3·kernel :5461 使用形） ---------- *)

Theorem piu1879_e3_lit : forall m : nat, NatLe 3 m ->
  QltT (1 # 100)%Q ((lw0m_xL m - 3)%Q).
Proof.
  intros m Hm.
  apply Qlt_to_QltT.
  unfold lw0m_xL.
  apply (Qlt_le_trans _ (lp_four * lp_odd 3 - 3)%Q _).
  - apply (proj2 (Qlt_minus_iff (1 # 100)%Q (lp_four * lp_odd 3 - 3)%Q)).
    apply (proj1 (Qlt_minus_iff (3 + 1 # 100)%Q (lp_four * lp_odd 3))).
    exact sc_lp_three_margin.
  - apply Qplus_le_compat.
    + setoid_replace (lp_four * lp_odd 3) with (lp_odd 3 * lp_four)%Q by ring.
      setoid_replace (lp_four * lp_odd m) with (lp_odd m * lp_four)%Q by ring.
      apply (Qmult_le_compat_r (lp_odd 3) (lp_odd m) lp_four).
      * apply sc_lp_odd_chain. apply NatLe_drop in Hm. lia.
      * apply sc_lp_four_nonneg.
    + apply Qle_refl.
Qed.

(* ---------- §2 el 字面释放（1/60·N=2·kernel :5460 使用形） ---------- *)

Theorem piu1879_el_lit : forall m : nat, NatLe 2 m ->
  QltT (1 # 60)%Q ((10 # 3)%Q - lw0m_xL m)%Q.
Proof.
  intros m Hm.
  apply Qlt_to_QltT.
  unfold lw0m_xL.
  apply (Qlt_le_trans _ ((10 / 3) - lp_four * (lp_odd 2 + lp_a 6))%Q _).
  - exact sc_lp_six_margin.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qopp_le_compat.
      setoid_replace (lp_four * lp_odd m) with (lp_odd m * lp_four)%Q by ring.
      setoid_replace (lp_four * (lp_odd 2 + lp_a 6))
        with ((lp_odd 2 + lp_a 6) * lp_four)%Q by ring.
      apply (Qmult_le_compat_r (lp_odd m) (lp_odd 2 + lp_a 6) lp_four).
      * apply sc_lp_odd_le_s6.
      * apply sc_lp_four_nonneg.
Qed.

(* ---------- §3 cert 承载位接合肢（1872 §8 Hcert 参数位形） ---------- *)

Theorem piu1879_cert4_le_lit60 : forall h : nat,
  Qle ((4 # 1)%Q / ((Z.of_nat (Datatypes.S h) # 1)%Q
        * q_fact (40 * h + 48)%nat)) (1 # 60)%Q.
Proof.
  intros h.
  apply (piu1872_bridge (4 # 1)%Q (1 # 1)%Q
           ((Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (40 * h + 48)%nat)%Q
           (60 # 1)%Q).
  - apply Qmult_lt_0_compat.
    + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z)
        by (apply Z2Nat.inj_lt; lia).
      unfold Qlt. cbn [Qnum Qden]. lia.
    + apply q_fact_pos.
  - vm_compute. reflexivity.
  - rewrite Qmult_1_l.
    apply (Qle_trans ((4 # 1)%Q * (60 # 1))%Q (q_fact 6)%Q).
    + vm_compute. discriminate.
    + apply (Qle_trans (q_fact 6)%Q (q_fact (40 * h + 48)%nat)).
      * apply piu1872_qfact_mono. lia.
      * (* q_fact(40h+48) ≤ (h+1)·q_fact(40h+48)：经显式 1* 形过渡
           （Qmult_le_compat_r 对裸 q_fact LHS 不可统一·彩排 R1 实录） *)
        apply (Qle_trans (q_fact (40 * h + 48)%nat)
                         ((1 * q_fact (40 * h + 48)%nat)%Q)).
        -- rewrite Qmult_1_l. apply Qle_refl.
        -- apply (Qmult_le_compat_r 1 ((Z.of_nat (Datatypes.S h) # 1)%Q)
                    (q_fact (40 * h + 48)%nat)).
           ++ assert (Hh : (0 <= Z.of_nat (Datatypes.S h))%Z)
                by (apply Z2Nat.inj_le; lia).
              unfold Qle. cbn [Qnum Qden]. lia.
           ++ apply Qlt_le_weak. apply q_fact_pos.
Qed.

(* Hcert 双肢合取形（eg := el := 1/60 实例化 1872 §8 两前提槽；
   合取词用库置面 And（S01 Set 面六词·QltT 承载）——彩排 R3 实录：
   stdlib /\ 系 Prop 级不能载 Set 面 QltT） *)
Theorem piu1879_cert_limbs : forall h : nat,
  And (Qle ((4 # 1)%Q / ((Z.of_nat (Datatypes.S h) # 1)%Q
        * q_fact (40 * h + 48)%nat)) (1 # 60)%Q)
      (QltT 0 (1 # 60)%Q).
Proof.
  intros h. split.
  - exact (piu1879_cert4_le_lit60 h).
  - apply Qlt_to_QltT. vm_compute. reflexivity.
Qed.

(* ========== 编译出口核对 ========== *)

Check piu1879_e3_lit.
Check piu1879_el_lit.
Check piu1879_cert4_le_lit60.
Check piu1879_cert_limbs.

Print Assumptions piu1879_e3_lit.
Print Assumptions piu1879_el_lit.
Print Assumptions piu1879_cert4_le_lit60.
Print Assumptions piu1879_cert_limbs.
