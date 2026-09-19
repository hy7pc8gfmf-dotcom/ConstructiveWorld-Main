(* ============================================================ *)
(* UpAblD1S3_fep_UpReqSteadyThermo.v —— FA-D1S3 批 D1-⑥ fa56-FEP 批    *)
(*   槽位（UpReqSteadyThermo.v，Real 面，语句逐字）：                    *)
(*     槽1 L82  real_partition_condition：real_eq Z_r (real_sum_over_S   *)
(*             (fun s => real_exp_neg (real_mult (real_inv_pos D D_pos)  *)
(*             (energy s))))                                             *)
(*     槽2 L95  real_transition_nonneg：forall s s', real_le real_zero   *)
(*             (real_transition s s')                                    *)
(*     槽3 L97  real_transition_normalization：forall s, real_eq         *)
(*             (real_sum_over_S (fun s' => real_transition s s')) one    *)
(*     槽4 L99  real_detailed_balance：forall s s', real_eq              *)
(*             (real_mult (real_boltzmann_prob s) (real_transition s s'))*)
(*             (real_mult (real_boltzmann_prob s') (real_transition s' s))) *)
(*   母本账（普查表钦定坐标＋面差诚实登记）：                            *)
(*     槽1 ← req_fep_partition_condition@UpReqFEPAttn.v:137（P2:428      *)
(*       五.2）：母本 req 面经 RealEnhancedReal 实例（S07:8566，字段映照  *)
(*       req:=real_eq/lt:=real_lt/mult:=real_mult/exp_neg:=real_exp_neg/  *)
(*       inv_pos:=real_inv_pos 逐位 delta 重合）落 Real 载体；sumf 取     *)
(*       sumd_sumf 消解实例、sum_ext 取 sumd_sum_ext；Z_r 取母本 Zf 实例   *)
(*       （exp_pos_fn_setoid 面，delta 展开＝real_exp_neg∘real_opp）、     *)
(*       energy 取 real_opp∘z0、D 取母本温度 T0——母本逐字实例化。        *)
(*     槽2 ← fa56_markov_kernel_nonneg@fa56_id_carrier.v:129 之 Real 面   *)
(*       同构件 real_boltzmann_dist_r_pos@S08_RealMainlineDPO.v:2488 直喂 *)
(*       （Id 面母本不可达 Real 载体：无 RealInterfaceEnhanced 实例，      *)
(*       FA-D1S1 偏差 4 同款复核；E751-A 同阶）。                         *)
(*     槽3 ← fa56_markov_kernel_normalized@fa56_id_carrier.v:139 之       *)
(*       Real 面镜像 rfep_boltzmann_normalized_real@UpReqRealFEP.v:340     *)
(*       直喂（单条 partition 前提由本件槽1 链显式供给；独立核轴向）。    *)
(*     槽4 ← fa56b_detailed_balance@fa56b_ext.v:195 之 Real 面镜像：      *)
(*       独立提议核 k(s,s'):=π(s')，mult_comm 收口同构直喂。              *)
(*   兑现装载（E354 装法同族）：转移核取独立提议核（与首参无关）；        *)
(*     Z 取定义为 boltzmann 非正规和实例（sumd 引擎），partition 前提     *)
(*     链显式承载。                                                       *)
(*   防重认领（20260919 实测）：Live_X 无 UpAblD1S1_*/UpAblD1S2_*/       *)
(*     UpAblP3S1_* 认领件；本四槽 Live_X 无既有同槽放电件。             *)
(*   纪律：零 git、原树零改、前缀 uabd1s3_ 全树零撞名；                  *)
(*     文尾 Print Assumptions 收尾；G3 提取探针内嵌一人一目录            *)
(*     _tuabd1s3_g3out（验后判读）。四关留痕 attn/logs/g1..4-UpAblD1S3_* *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
Require Import UpReqFEPAttn.
Require Import S08_RealMainlineDPO.
Require Import UpReqRealFEP.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Import RealInterfaceEnhancedMod.

(* ---- 载体件：boltzmann 非正规和 Z 实例（sumd 引擎） ---- *)
Definition uabd1s3_fep_st_Z (S0 : Set) (enum0 : list S0)
  (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D) : Real :=
  sumd_sumf S0 enum0
    (fun s : S0 => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))).

Lemma uabd1s3_fep_st_Z_pos :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D),
    real_lt real_zero (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos).
Proof.
  intros S0 enum0 Hne base_loss D D_pos.
  exact (sumd_sum_pos S0 enum0
          (fun s : S0 => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s)))
          Hne
          (fun s : S0 => real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (base_loss s)))).
Qed.

(* ---- 载体件：Boltzmann 分布 π 实例（real_boltzmann_dist_r 装配） ---- *)
Definition uabd1s3_fep_st_dist (S0 : Set) (enum0 : list S0)
  (Hne : Not (enum0 = nil)) (base_loss : S0 -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (s : S0) : Real :=
  real_boltzmann_dist_r S0 base_loss D D_pos
    (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
    (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos) s.

(* ---- 载体件：独立提议核 k(s,s'):=π(s')（与首参无关，fa56b 同构） ---- *)
Definition uabd1s3_fep_st_kernel (S0 : Set) (enum0 : list S0)
  (Hne : Not (enum0 = nil)) (base_loss : S0 -> Real) (D : Real)
  (D_pos : real_lt real_zero D) : S0 -> S0 -> Real :=
  fun _ s' => uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s'.

(* ---- 槽1 L82 real_partition_condition（母本 req_fep_partition_condition *)
(*    @UpReqFEPAttn:137 经 RealEnhancedReal 实例逐字实例化） ---- *)
Theorem uabd1s3_fep_st_real_partition_condition :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (z0 : S0 -> Real) (T0 : Real) (HT0 : real_lt real_zero T0),
    real_eq (sumd_sumf S0 enum0
              (fun s : S0 => real_exp_neg
                              (real_opp (real_mult (real_inv_pos T0 HT0) (z0 s)))))
            (sumd_sumf S0 enum0
              (fun s : S0 => real_exp_neg
                              (real_mult (real_inv_pos T0 HT0) (real_opp (z0 s))))).
Proof.
  intros S0 enum0 Hne z0 T0 HT0.
  exact (req_fep_partition_condition S0 (sumd_sumf S0 enum0)
          (sumd_sum_ext S0 enum0) z0 T0 HT0).
Qed.

(* ---- 槽2 L95 real_transition_nonneg（real_boltzmann_dist_r_pos 严格形   *)
(*    直喂，real_lt_le_iff@S02:3179 升 le 一跳；偏差账登记） ---- *)
Theorem uabd1s3_fep_st_real_transition_nonneg :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s s' : S0),
    real_le real_zero (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s').
Proof.
  intros S0 enum0 Hne base_loss D D_pos s s'.
  apply real_lt_le_iff. left.
  exact (real_boltzmann_dist_r_pos S0 base_loss D D_pos
          (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
          (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos) s').
Qed.

(* ---- 槽3 L97 real_transition_normalization（rfep_boltzmann_normalized_real *)
(*    直喂；partition 前提由 Z 定义件 real_eq_refl 承载） ---- *)
Theorem uabd1s3_fep_st_real_transition_normalization :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s : S0),
    real_eq (sumd_sumf S0 enum0
              (fun s' : S0 => uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s'))
            real_one.
Proof.
  intros S0 enum0 Hne base_loss D D_pos s.
  exact (rfep_boltzmann_normalized_real S0 (sumd_sumf S0 enum0)
          (sumd_sum_ext S0 enum0) (sumd_sum_linear S0 enum0)
          base_loss D D_pos
          (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
          (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos)
          (real_eq_refl _)).
Qed.

(* ---- 槽4 L99 real_detailed_balance（fa56b 独立提议核镜像，mult_comm 收口） ---- *)
Theorem uabd1s3_fep_st_real_detailed_balance :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s s' : S0),
    real_eq (real_mult (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s)
                       (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s'))
            (real_mult (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s')
                       (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s' s)).
Proof.
  intros S0 enum0 Hne base_loss D D_pos s s'.
  exact (real_mult_comm (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s)
                        (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s')).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_fep_st_Z.ml" uabd1s3_fep_st_Z.

Print Assumptions uabd1s3_fep_st_Z_pos.
Print Assumptions uabd1s3_fep_st_real_partition_condition.
Print Assumptions uabd1s3_fep_st_real_transition_nonneg.
Print Assumptions uabd1s3_fep_st_real_transition_normalization.
Print Assumptions uabd1s3_fep_st_real_detailed_balance.
