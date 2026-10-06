(* ============================================================ *)
(* abl_redischarge_fdiv2_half.v —— 两点 f-散度骨架 q/s/s' 典范参数    *)
(*   实例化消解件                                                     *)
(* 模块名：abl_redischarge_fdiv2_half                                 *)
(* 数学使命：前件 Section FDivTwoPoint（q s s' fa fb f1 cdown cup 系） *)
(*   在典范参数下的零参数闭式推论：                                   *)
(*     q := bp_half（=1/2：inv_pos(1+1) 于 kv_two_R_pos），           *)
(*     s := bp_sp（=3/2：real_plus real_one bp_half），               *)
(*     s' := bp_half（=1/2），                                        *)
(*     f 数据取 χ² 典范形（前件 §2.1 df2_inst_chisq_fa：f(u)=(u−1)²，  *)
(*     fa:=f(3/2)、fb:=f(1/2)、f1:=0），照管斜率 cdown:=cup:=0        *)
(*     （χ² 平方形在归一化点 u=1 的真切距斜率，前件 §2.1 同款口径）。  *)
(*   出 df2_half_j_nonneg（J_f ≥ 0 闭式）与 df2_half_j_le_cs          *)
(*   （超额 ≤ χ²-比值形闭式）两零参数推论；语句面全 Set 层             *)
(*   （real_eq/real_lt/real_le_b——Bishop ∀eps>0 形，零 Or 零 Prop）。  *)
(* 依赖清单：前件 abl_div_fdiv2_skeleton（本池拷贝链编，及其三前件     *)
(*   abl_div_chisq_twopoint/abl_div_kl_chisq_twopoint/                *)
(*   abl_div_hellinger_twopoint）；PinskerTwoPoint（p2_one_minus）；    *)
(*   UpRealLeB 系（real_le_b/leb3_le_b_eq_l/real_lt_plus_r_zero）；    *)
(*   UpKVDrift_P2（kv_two_R_pos/kv_one_mult_l/kv_distrib_r）；         *)
(*   S02/S07/S08（real_distrib/real_plus_opp/real_plus_assoc/         *)
(*   real_plus_zero/real_inv_pos_correct/real_inv_pos_pos/            *)
(*   RealSetoid.real_eq_mult_compat/real_lt_id_l/real_lt_plus_compat）。*)
(* 构造性注记：零承认／零经典逻辑；全部证书真构造；Hup 证书走前件      *)
(*   §3.0b 尾消去件 df2_sub_zero_r + leb3_le_b_eq_l 换形 +             *)
(*   real_lt_plus_r_zero 显式 λ（零承认）；归一化恒等 bp_norm_half     *)
(*   为本件新证代数链                                                  *)
(*   （half+half==1 → 1−half==half → half==half²+half² → 照管和对消）。*)
(* 编译配方：标准配方，四前件先、本件后                                *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh *)
(*   && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> && nice -19  *)
(*   rocq c -native-compiler no -Q                                      *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 *)
(*   "" <件>.v（abl_div_chisq_twopoint → kl_chisq → hellinger →          *)
(*   fdiv2_skeleton → 本件）。                                           *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring QArith.Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import PinskerTwoPoint.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import G07_KLWall.
Require Import G08_Gibbs.
Require Import UpReqTrainingEquiv.
Require Import UpReqPinskerTransport.
Require Import UpKVDrift_P2.
Require Import abl_div_chisq_twopoint.
Require Import abl_div_kl_chisq_twopoint.
Require Import abl_div_hellinger_twopoint.
Require Import abl_div_fdiv2_skeleton.

(* ---------- §0 典范常数：q := 1/2、s := 3/2、s' := 1/2 ---------- *)

Definition bp_half : Real :=
  real_inv_pos (real_plus real_one real_one) kv_two_R_pos.

Definition bp_sp : Real := real_plus real_one bp_half.

Lemma bp_half_pos : real_lt real_zero bp_half.
Proof. exact (real_inv_pos_pos (real_plus real_one real_one) kv_two_R_pos). Qed.

Lemma bp_sp_pos : real_lt real_zero bp_sp.
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero) bp_sp).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat.
    + exact real_lt_zero_one.
    + exact bp_half_pos.
Qed.

(* ---------- §1 半位代数三件（典范参数的归一化燃料） ---------- *)

(* ① half + half == 1 *)
Lemma bp_half_sum_one : real_eq (real_plus bp_half bp_half) real_one.
Proof.
  apply (real_eq_trans
           (real_plus bp_half bp_half)
           (real_mult (real_plus real_one real_one) bp_half)
           real_one).
  - apply (real_eq_trans
             (real_plus bp_half bp_half)
             (real_plus (real_mult real_one bp_half)
                        (real_mult real_one bp_half))
             (real_mult (real_plus real_one real_one) bp_half)).
    + apply (RealSetoid.real_eq_plus_compat bp_half bp_half
               (real_mult real_one bp_half) (real_mult real_one bp_half)
               (real_eq_sym (real_mult real_one bp_half) bp_half
                  (kv_one_mult_l bp_half))
               (real_eq_sym (real_mult real_one bp_half) bp_half
                  (kv_one_mult_l bp_half))).
    + apply real_eq_sym. exact (kv_distrib_r real_one real_one bp_half).
  - exact (real_inv_pos_correct (real_plus real_one real_one) kv_two_R_pos).
Qed.

(* ② half == half² + half² *)
Lemma bp_half_sq2 :
  real_eq bp_half
          (real_plus (real_mult bp_half bp_half) (real_mult bp_half bp_half)).
Proof.
  apply (real_eq_trans bp_half
           (real_mult bp_half (real_plus bp_half bp_half))
           (real_plus (real_mult bp_half bp_half) (real_mult bp_half bp_half))).
  - apply real_eq_sym.
    apply (real_eq_trans
             (real_mult bp_half (real_plus bp_half bp_half))
             (real_mult bp_half real_one)
             bp_half).
    + apply (RealSetoid.real_eq_mult_compat bp_half
               (real_plus bp_half bp_half) bp_half real_one
               (real_eq_refl bp_half) bp_half_sum_one).
    + apply (real_eq_trans (real_mult bp_half real_one)
               (real_mult real_one bp_half) bp_half
               (real_mult_comm bp_half real_one)
               (kv_one_mult_l bp_half)).
  - exact (real_distrib bp_half bp_half bp_half).
Qed.

(* ③ 1 − half == half *)
Lemma bp_one_minus_half : real_eq (p2_one_minus bp_half) bp_half.
Proof.
  apply (real_eq_trans
           (real_plus real_one (real_opp bp_half))
           (real_plus (real_plus bp_half bp_half) (real_opp bp_half))
           bp_half).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_opp bp_half)
             (real_plus bp_half bp_half) (real_opp bp_half)
             (real_eq_sym (real_plus bp_half bp_half) real_one
                bp_half_sum_one)
             (real_eq_refl (real_opp bp_half))).
  - apply (real_eq_trans
             (real_plus (real_plus bp_half bp_half) (real_opp bp_half))
             (real_plus bp_half (real_plus bp_half (real_opp bp_half)))
             bp_half).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans
               (real_plus bp_half (real_plus bp_half (real_opp bp_half)))
               (real_plus bp_half real_zero)
               bp_half).
      * apply (RealSetoid.real_eq_plus_compat bp_half
                 (real_plus bp_half (real_opp bp_half)) bp_half real_zero
                 (real_eq_refl bp_half) (real_plus_opp bp_half)).
      * apply real_plus_zero.
Qed.

Lemma bp_half_one_minus_pos : real_lt real_zero (p2_one_minus bp_half).
Proof.
  apply (RealSetoid.real_lt_id_r real_zero bp_half (p2_one_minus bp_half)
           (real_eq_sym (p2_one_minus bp_half) bp_half bp_one_minus_half)
           bp_half_pos).
Qed.

(* ---------- §2 归一化恒等：q·s + (1−q)·s' == 1 于典范参数 ---------- *)
(*   (1/2)·(3/2) + (1/2)·(1/2) == 3/4 + 1/4 == 1（χ² 比值数据实现）。   *)
Lemma bp_norm_half :
  real_eq
    (real_plus (real_mult bp_half bp_sp)
               (real_mult (p2_one_minus bp_half) bp_half))
    real_one.
Proof.
  apply (real_eq_trans
           (real_plus (real_mult bp_half bp_sp)
                      (real_mult (p2_one_minus bp_half) bp_half))
           (real_plus (real_plus bp_half (real_mult bp_half bp_half))
                      (real_mult bp_half bp_half))
           real_one).
  - (* 双 summand 分别换形：half·(1+half) == half + half²；
       (1−half)·half == half·half（bp_one_minus_half 乘入） *)
    apply (RealSetoid.real_eq_plus_compat
             (real_mult bp_half bp_sp)
             (real_mult (p2_one_minus bp_half) bp_half)
             (real_plus bp_half (real_mult bp_half bp_half))
             (real_mult bp_half bp_half)).
    + apply (real_eq_trans
               (real_mult bp_half bp_sp)
               (real_plus (real_mult bp_half real_one)
                          (real_mult bp_half bp_half))
               (real_plus bp_half (real_mult bp_half bp_half))).
      * exact (real_distrib bp_half real_one bp_half).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult bp_half real_one) (real_mult bp_half bp_half)
                 bp_half (real_mult bp_half bp_half)
                 (real_eq_trans (real_mult bp_half real_one)
                    (real_mult real_one bp_half) bp_half
                    (real_mult_comm bp_half real_one)
                    (kv_one_mult_l bp_half))
                 (real_eq_refl (real_mult bp_half bp_half))).
    + apply (RealSetoid.real_eq_mult_compat
               (p2_one_minus bp_half) bp_half bp_half bp_half
               bp_one_minus_half (real_eq_refl bp_half)).
  - (* (half + half²) + half² == half + (half² + half²) == half + half == 1 *)
    apply (real_eq_trans
             (real_plus (real_plus bp_half (real_mult bp_half bp_half))
                        (real_mult bp_half bp_half))
             (real_plus bp_half (real_plus (real_mult bp_half bp_half)
                                           (real_mult bp_half bp_half)))
             real_one).
    + apply real_eq_sym. apply real_plus_assoc.
    + apply (real_eq_trans
               (real_plus bp_half
                  (real_plus (real_mult bp_half bp_half)
                             (real_mult bp_half bp_half)))
               (real_plus bp_half bp_half)
               real_one).
      * apply (RealSetoid.real_eq_plus_compat bp_half
                 (real_plus (real_mult bp_half bp_half)
                            (real_mult bp_half bp_half))
                 bp_half bp_half
                 (real_eq_refl bp_half)
                 (real_eq_sym bp_half
                    (real_plus (real_mult bp_half bp_half)
                               (real_mult bp_half bp_half))
                    bp_half_sq2)).
      * exact bp_half_sum_one.
Qed.

(* ---------- §3 χ² 典范 f 数据与照管证书（斜率全零，前件 §2.1 口径） --- *)

Definition bp_fa : Real := df2_inst_chisq_fa bp_sp.
Definition bp_fb : Real := df2_inst_chisq_fa bp_half.

(* Hlow 双证书：0·(u−1) == 0 ≤_B (u−1)²（前件 df2_inst_chisq_hlow 直引） *)
Lemma bp_Hlow_s :
  real_le_b
    (real_mult real_zero (real_plus bp_sp (real_opp real_one)))
    bp_fa.
Proof. exact (df2_inst_chisq_hlow bp_sp). Qed.

Lemma bp_Hlow_s1 :
  real_le_b
    (real_mult real_zero (real_plus bp_half (real_opp real_one)))
    bp_fb.
Proof. exact (df2_inst_chisq_hlow bp_half). Qed.

(* Hup 双证书（cup := 0）：X − half·(0·(u−1)) == X ⟹ ≤_B X
   （df2_sub_zero_r 尾消去 + real_lt_plus_r_zero 显式 λ；x2 与 y 换算
   走 fa 定义展开的转换兼容） *)
Lemma bp_Hup_s :
  real_le_b
    (real_plus (real_mult bp_half bp_fa)
               (real_opp (real_mult bp_half
                  (real_mult real_zero
                     (real_plus bp_sp (real_opp real_one))))))
    (real_mult bp_half
       (real_mult (real_plus bp_sp (real_opp real_one))
                  (real_plus bp_sp (real_opp real_one)))).
Proof.
  apply (leb3_le_b_eq_l
           (real_mult bp_half bp_fa)
           (real_plus (real_mult bp_half bp_fa)
              (real_opp (real_mult bp_half
                 (real_mult real_zero
                    (real_plus bp_sp (real_opp real_one))))))
           (real_mult bp_half
              (real_mult (real_plus bp_sp (real_opp real_one))
                         (real_plus bp_sp (real_opp real_one))))).
  - exact (real_eq_sym
             (real_plus (real_mult bp_half bp_fa)
                (real_opp (real_mult bp_half
                   (real_mult real_zero
                      (real_plus bp_sp (real_opp real_one))))))
             (real_mult bp_half bp_fa)
             (df2_sub_zero_r (real_mult bp_half bp_fa) bp_half
                (real_plus bp_sp (real_opp real_one)))).
  - exact (leb3_le_b_refl (real_mult bp_half bp_fa)).
Qed.

Lemma bp_Hup_s1 :
  real_le_b
    (real_plus (real_mult (p2_one_minus bp_half) bp_fb)
               (real_opp (real_mult (p2_one_minus bp_half)
                  (real_mult real_zero
                     (real_plus bp_half (real_opp real_one))))))
    (real_mult (p2_one_minus bp_half)
       (real_mult (real_plus bp_half (real_opp real_one))
                  (real_plus bp_half (real_opp real_one)))).
Proof.
  apply (leb3_le_b_eq_l
           (real_mult (p2_one_minus bp_half) bp_fb)
           (real_plus (real_mult (p2_one_minus bp_half) bp_fb)
              (real_opp (real_mult (p2_one_minus bp_half)
                 (real_mult real_zero
                    (real_plus bp_half (real_opp real_one))))))
           (real_mult (p2_one_minus bp_half)
              (real_mult (real_plus bp_half (real_opp real_one))
                         (real_plus bp_half (real_opp real_one))))).
  - exact (real_eq_sym
             (real_plus (real_mult (p2_one_minus bp_half) bp_fb)
                (real_opp (real_mult (p2_one_minus bp_half)
                   (real_mult real_zero
                      (real_plus bp_half (real_opp real_one))))))
             (real_mult (p2_one_minus bp_half) bp_fb)
             (df2_sub_zero_r (real_mult (p2_one_minus bp_half) bp_fb)
                (p2_one_minus bp_half)
                (real_plus bp_half (real_opp real_one)))).
  - exact (leb3_le_b_refl (real_mult (p2_one_minus bp_half) bp_fb)).
Qed.

(* ---------- §4 零参数闭式推论（典范参数全消解） ---------- *)

(* J_f ≥ 0 于 χ² 典范数据：J = (1/2)·f(3/2) + (1/2)·f(1/2) ≥ 0 *)
Theorem df2_half_j_nonneg :
  real_le_b real_zero (df2_j bp_half bp_fa bp_fb).
Proof.
  exact (df2_j_nonneg bp_half bp_sp bp_half
           bp_half_pos bp_half_one_minus_pos bp_norm_half
           bp_fa bp_fb real_zero bp_Hlow_s bp_Hlow_s1).
Qed.

(* 超额 ≤ χ²-比值形于典范数据（cup := 0 尾消去形） *)
Theorem df2_half_j_le_cs :
  real_le_b
    (real_plus
       (real_plus (real_mult bp_half bp_fa)
                  (real_opp (real_mult bp_half
                     (real_mult real_zero
                        (real_plus bp_sp (real_opp real_one))))))
       (real_plus (real_mult (p2_one_minus bp_half) bp_fb)
                  (real_opp (real_mult (p2_one_minus bp_half)
                     (real_mult real_zero
                        (real_plus bp_half (real_opp real_one)))))))
    (df2_cs_inst bp_half bp_sp bp_half).
Proof.
  exact (df2_j_le_cs bp_half bp_sp bp_half bp_fa bp_fb real_zero
           bp_Hup_s bp_Hup_s1).
Qed.

(* ---------- §5 公理审计（Print Assumptions 取证面） ---------- *)

Print Assumptions bp_half_pos.
Print Assumptions bp_sp_pos.
Print Assumptions bp_half_sum_one.
Print Assumptions bp_half_sq2.
Print Assumptions bp_one_minus_half.
Print Assumptions bp_norm_half.
Print Assumptions bp_Hlow_s.
Print Assumptions bp_Hlow_s1.
Print Assumptions bp_Hup_s.
Print Assumptions bp_Hup_s1.
Print Assumptions df2_half_j_nonneg.
Print Assumptions df2_half_j_le_cs.
