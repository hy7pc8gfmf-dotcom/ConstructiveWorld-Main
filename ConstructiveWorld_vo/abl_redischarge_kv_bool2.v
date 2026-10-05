(* ===================================================================== *)
(*  模块名：abl_redischarge_kv_bool2 —— 再次消解件 1：abl_kv_sat_drift      *)
(*    最小世界实例化消解                                                     *)
(* 使命：前件 Section KVSatDrift（Tok/states/K/delta/c 系 14 参）在          *)
(*    典范参数下的零参数闭式推论 kvs_drift_sat_bool2（tvL 孪生               *)
(*    kvs_drift_sat_tv_bool2 同出）：最小世界 Tok:=bool 两态                 *)
(*    states:=[true;false]，K:=显式对称常值核 bp_half:=1/2（对称平凡成立）， *)
(*    keep:=恒真掩码，delta:=real_one，c:=real_zero（恒真掩码下逐出行        *)
(*    误差 tv_row==0 的闭式证书链：kv_tvrow_split 分部 + kv_gsum_scaled/     *)
(*    kv_scaledZ_tail 缩放桥 + 尾和零——硬核实例化，非折算件）。               *)
(* 构造性注记：语句面全 Set 层（real_eq/real_lt/real_le/And/sigT）；         *)
(*    states_ne 以 S01 Not（Set 编码 A->Empty_set）承载；keep_nonempty       *)
(*    以 sigT+And+Id+InT 落实（pair 显式构造；conj 为 Prop 构造子不可用，     *)
(*    照 Set 层纪律先例）。                                                  *)
(* 依赖清单：前件 abl_kv_sat_drift（本池拷贝链编：kvs_drift_sat/             *)
(*    kvs_drift_sat_tv/kvs_UU/kvs_KEV/kvs_kI/kvs_DD/kvs_board）；            *)
(*    UpKVDrift_P2（kv_N_pos/kv_ofnat_S_pos/kv_sum_const_list/               *)
(*    kv_one_mult_l/real_mult_zero/kv_gsum_scaled/kv_scaledZ_tail/           *)
(*    kv_tvrow_split/Z_keep/K_ev/tv_row/tail_row）；S07（real_inv_pos_ext/   *)
(*    real_inv_pos_pos/real_lt_zero_one/RealSetoid.real_eq_le/               *)
(*    real_eq_plus_compat/real_eq_trans/real_le_trans/real_le_refl）。        *)
(*    零承认／零经典逻辑；全部实例证书为真构造（Krow 走常数和                *)
(*    +inv_pos_correct 单位元链；delta_minor 走 one_mult_l+inv_pos_ext       *)
(*    换元；Hrow 走 tv_row 分部—缩放—尾零三桥）。Print Assumptions 逐条取证。 *)
(* 编译配方：source <toolchain>/env.sh && unset COQLIB ROCQLIB &&             *)
(*    ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q <world>       *)
(*    "" abl_kv_sat_drift.v（先）&& 同配方编本件（后）。                      *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpKVDrift_P2.
Require Import UpTVDoeblin.
Require Import abl_kv_sat_drift.

(* ---------- 0. 最小世界数据（bool 两态＋对称常值核） ---------- *)

Definition bp_states : list bool := (true :: false :: nil).

(* 非空：S01 Not（Set 编码）承载；cons≠nil 以 inversion 空支闭合 *)
Definition bp_states_ne : Not (Id bp_states nil).
Proof.
  intros H. inversion H.
Defined.

(* 显式对称常值核：K(s,s') := 1/2（对称性对常值核平凡成立） *)
Definition bp_half : Real :=
  real_inv_pos (real_of_nat 2) (kv_ofnat_S_pos 1).

Definition bp_K : bool -> bool -> Real := fun _ _ => bp_half.

(* 恒真掩码与其非空契约（sigT+And+Id+InT 全 Set 落实） *)
Definition bp_keep : bool -> bool := fun _ => true.

Definition bp_keep_nonempty :
  {s : bool & And (Id (bp_keep s) true) (InT s bp_states)} :=
  existT _ true (pair id_refl (@InT_here bool true (false :: nil))).

(* ---------- 1. 核行随机证书：Σ_s' K(s,s') == 1 ---------- *)

Lemma bp_Krow : forall s : bool,
  real_eq (real_list_sum bool (fun s' : bool => bp_K s s') bp_states) real_one.
Proof.
  intro s.
  apply (real_eq_trans
           (real_list_sum bool (fun s' : bool => bp_K s s') bp_states)
           (real_mult (real_of_nat (length bp_states)) bp_half)
           real_one).
  - exact (kv_sum_const_list bool bp_half bp_states).
  - exact (real_inv_pos_correct (real_of_nat 2) (kv_ofnat_S_pos 1)).
Qed.

Lemma bp_Kpos : forall s s' : bool, real_lt real_zero (bp_K s s').
Proof.
  intros s s'.
  exact (real_inv_pos_pos (real_of_nat 2) (kv_ofnat_S_pos 1)).
Qed.

(* ---------- 2. delta := 1 证书与逐点 minorization ---------- *)

Definition bp_delta : Real := real_one.

Lemma bp_delta_pos : real_lt real_zero bp_delta.
Proof. exact real_lt_zero_one. Qed.

Lemma bp_delta_le : real_le bp_delta real_one.
Proof. exact (real_le_refl real_one). Qed.

Lemma bp_delta_minor : forall s s' : bool,
  real_le
    (real_mult bp_delta
       (kvs_UU bool bp_states bp_states_ne bp_K bp_Krow bp_keep
          bp_keep_nonempty s'))
    (bp_K s s').
Proof.
  intros s s'.
  apply (real_le_trans
           (real_mult real_one
              (kvs_UU bool bp_states bp_states_ne bp_K bp_Krow bp_keep
                 bp_keep_nonempty s'))
           (kvs_UU bool bp_states bp_states_ne bp_K bp_Krow bp_keep
              bp_keep_nonempty s')
           (bp_K s s')).
  - apply (RealSetoid.real_eq_le _ _ (kv_one_mult_l
             (kvs_UU bool bp_states bp_states_ne bp_K bp_Krow bp_keep
                bp_keep_nonempty s'))).
  - (* kvs_UU s' == 1/2：同底异正性证书的 inv_pos_ext 换元
       （kvs_UU 展开后 length bp_states 归约为 2，与 bp_half 同底） *)
    apply (RealSetoid.real_eq_le _ _ (real_inv_pos_ext
             (real_of_nat 2) (real_of_nat 2)
             (kv_N_pos bool bp_states bp_states_ne bp_K bp_Krow bp_keep
                bp_keep_nonempty)
             (kv_ofnat_S_pos 1)
             (real_eq_refl (real_of_nat 2)))).
Qed.

(* ---------- 3. c := 0 证书：恒真掩码下逐行误差 tv_row == 0 ---------- *)

Definition bp_c : Real := real_zero.

(* 尾和零：掩码恒真时 tail_row s ≡ Σ 0 == 2·0 == 0 *)
Lemma bp_tail_zero : forall s : bool,
  real_eq
    (tail_row bool bp_states bp_K bp_keep s)
    real_zero.
Proof.
  intro s. unfold tail_row.
  apply (real_eq_trans
           (real_list_sum bool
              (fun s' : bool =>
                 if bp_keep s' then real_zero else bp_K s s')
              bp_states)
           (real_mult (real_of_nat 2) real_zero)
           real_zero).
  - exact (kv_sum_const_list bool real_zero bp_states).
  - exact (real_mult_zero (real_of_nat 2)).
Qed.

(* tv_row == 0：分部（kv_tvrow_split）＋keep 支和缩放双桥
   （kv_gsum_scaled/kv_scaledZ_tail 归于尾和）＋尾和双份吸收 *)
Lemma bp_tvrow_zero : forall s : bool,
  real_eq
    (tv_row bool bp_states bp_K bp_Kpos bp_keep bp_keep_nonempty s)
    real_zero.
Proof.
  intro s.
  eapply real_eq_trans.
  - exact (kv_tvrow_split bool bp_states bp_K bp_Krow bp_Kpos bp_keep
             bp_keep_nonempty s).
  - eapply real_eq_trans.
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum bool
                  (fun w : bool =>
                     if bp_keep w
                     then real_minus_r
                            (K_ev bool bp_states bp_K bp_Kpos bp_keep
                               bp_keep_nonempty s w)
                            (bp_K s w)
                     else real_zero)
                  bp_states)
               (tail_row bool bp_states bp_K bp_keep s)
               (tail_row bool bp_states bp_K bp_keep s)
               (tail_row bool bp_states bp_K bp_keep s)).
      * eapply real_eq_trans.
        -- exact (kv_gsum_scaled bool bp_states bp_K bp_Kpos bp_keep
                    bp_keep_nonempty s).
        -- exact (kv_scaledZ_tail bool bp_states bp_K bp_Krow bp_Kpos bp_keep
                    bp_keep_nonempty s).
      * apply real_eq_refl.
    + apply (real_eq_trans
               (real_plus (tail_row bool bp_states bp_K bp_keep s)
                          (tail_row bool bp_states bp_K bp_keep s))
               (real_plus real_zero real_zero)
               real_zero).
      * apply (RealSetoid.real_eq_plus_compat
                 (tail_row bool bp_states bp_K bp_keep s)
                 (tail_row bool bp_states bp_K bp_keep s)
                 real_zero real_zero).
        -- exact (bp_tail_zero s).
        -- exact (bp_tail_zero s).
      * apply real_plus_zero.
Qed.

Lemma bp_Hrow : forall s : bool,
  real_le
    (tv_row bool bp_states bp_K bp_Kpos bp_keep bp_keep_nonempty s)
    bp_c.
Proof.
  intro s. apply (RealSetoid.real_eq_le _ _ (bp_tvrow_zero s)).
Qed.

(* ---------- 4. 零参数闭式推论（典范实例全消解） ---------- *)

Theorem kvs_drift_sat_bool2 : forall (n : nat) (mu : bool -> Real) (eps : Real),
  real_eq (real_list_sum bool mu bp_states) real_one ->
  (forall s : bool, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  And
    (real_le
       (kvs_DD bool bp_states
          (kvs_kevI bool bp_states bp_K bp_Kpos bp_keep bp_keep_nonempty n mu)
          (kvs_kI bool bp_states bp_K n mu))
       (real_plus (real_mult (real_of_nat n) bp_c) eps))
    (real_le
       (kvs_DD bool bp_states
          (kvs_kevI bool bp_states bp_K bp_Kpos bp_keep bp_keep_nonempty n mu)
          (kvs_kI bool bp_states bp_K n mu))
       (real_plus (kvs_board bp_delta bp_delta_pos bp_c) eps)).
Proof.
  intros n mu eps Hnorm Hnn Heps.
  exact (kvs_drift_sat bool bp_states bp_states_ne bp_K bp_Krow bp_Kpos
           bp_keep bp_keep_nonempty bp_delta bp_delta_pos bp_delta_le
           bp_delta_minor bp_c bp_Hrow n mu eps Hnorm Hnn Heps).
Qed.

(* tvL 孪生闭式（半和口径；同实例同证书全消解） *)
Theorem kvs_drift_sat_tv_bool2 : forall (n : nat) (mu : bool -> Real) (eps : Real),
  real_eq (real_list_sum bool mu bp_states) real_one ->
  (forall s : bool, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  real_le
    (tvL bool bp_states
       (kvs_kevI bool bp_states bp_K bp_Kpos bp_keep bp_keep_nonempty n mu)
       (kvs_kI bool bp_states bp_K n mu))
    (real_mult
       (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
       (real_plus (kvs_board bp_delta bp_delta_pos bp_c) eps)).
Proof.
  intros n mu eps Hnorm Hnn Heps.
  exact (kvs_drift_sat_tv bool bp_states bp_states_ne bp_K bp_Krow bp_Kpos
           bp_keep bp_keep_nonempty bp_delta bp_delta_pos bp_delta_le
           bp_delta_minor bp_c bp_Hrow n mu eps Hnorm Hnn Heps).
Qed.

(* ---------- 5. 公理审计（Print Assumptions 取证面） ---------- *)

Print Assumptions bp_Krow.
Print Assumptions bp_Kpos.
Print Assumptions bp_delta_minor.
Print Assumptions bp_tail_zero.
Print Assumptions bp_tvrow_zero.
Print Assumptions bp_Hrow.
Print Assumptions kvs_drift_sat_bool2.
Print Assumptions kvs_drift_sat_tv_bool2.
