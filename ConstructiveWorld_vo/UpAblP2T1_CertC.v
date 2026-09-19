(* ============================================================ *)
(* UpAblP2T1_CertC.v —— H2 席（T2 复合/多 eps 升格专责席·复验模式）          *)
(*   论文2 T 簇行 27（T2＝UpRealLeB 结论 9(e)/(f)）独立复验＋独立面重建并存件  *)
(* 工单：任务切分令（H2 主攻 T2）＋协调中继令（G1 已收账，转复验模式）          *)
(* 对账基准：G1 席 UpAblP2T1_CertB.v 四具名件 p2t1b_T2_*_supply（直引          *)
(*   UpRealLeB2 F.4-F.7）；本件与其并存互证，零触其文件、零重认领。            *)
(*                                                              *)
(* 【复验模式定谳（协调令 20260920）】T2 已由 G1 直引收账。本件按两可处置之     *)
(*   「独立面」路径施工：                                                      *)
(*   ① 9(e) 三件自源件独立重建——证明链只消费源件                              *)
(*     （real_abs_le_quad_eps@S08:4901 五前件＋四分支内件链、                  *)
(*       real_quad_t_le_h_eps@S08:4965、real_abs_h_sq_le_eps@S09:1087）        *)
(*     ＋UpRealLeB plain-eps 完成器 real_le_closure_b_one（Part D.0 特化完成），*)
(*     不经 UpRealLeB2 F.4-F.6、不经 CertB——多 eps 组合闭包单跳                *)
(*     （尾自由 eps 经完成器消去，eps1/eps2/内嵌 |h| 因子随固定端并入右端），    *)
(*     与 A1 席路线注「非真墙、组合闭包单跳」逐字对齐。                         *)
(*   ② 9(f) 一件（real_db_breaking_bound_eps@S10:979，复合系数形）按           *)
(*     「直引收账」路径零施工登记：语句面逐字重述，类型装配机检对照 CertB       *)
(*     具名件（类型不合即编译炸＝复验带响）；其源件签名面与复合系数完成链       *)
(*     （F.1 非负系数完成器）承 G1 席探针与四关账，本件不重跑、如实注记边界。   *)
(*   ③ 交叉核验面：四具名 p2t1b 件逐一以本件独立重述语句做类型装配 Check        *)
(*     ＋文尾假设面打印重跑（CertB 四件＋本件三件＋登记件），G4 全链核验覆盖    *)
(*     CertB 与 UpRealLeB2 整链。                                              *)
(*                                                              *)
(* 零承认件：纯构造性，语句面全 Set 层（Id/Not/Or 别名、real_lt/real_le/       *)
(* real_le_b/real_eq 面），零裸命题入语句与前件位；Qed 全闭合。                *)
(* 原树零改；不入 order.txt/_CoqProject；禁触 9.0 任何产物。                   *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpAblP2T1_CertB.
From Stdlib Require Import Extraction.

(* ################ 一、9(e) 独立面：自源件完成器单跳重建 ##################### *)

(* e-1（盘点 #24）：|X| ≤_B 2t²＋(eps1＋eps2)。
   源件结论尾带全称 eps 余量（plain-eps 字面），故组合闭包单跳即达：
   real_le_closure_b_one 收拢全称 eps，五前件中四件保留前提位、Heps 入完成器。 *)
Theorem p2t1c_T2_abs_le_quad_supply : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB Heps1 Heps2.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_abs_le_quad_eps X t eps1 eps2 eps HXA HXB Heps1 Heps2 Heps).
Qed.

(* e-2（盘点 #25）：2(h/x)² ≤_B (1/2)·eps·|h|。
   余量内嵌 |h| 因子随固定端并入右端；源件 eps' 为全称求和余量，单跳消去。 *)
Theorem p2t1c_T2_quad_t_le_h_supply : forall (x h eps : Real)
    (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_quad_t_le_h_eps x h eps eps' Hx Hh Heps Heps').
Qed.

(* e-3（盘点 #28）：A|h|² ≤_B (A·eps3)·|h|。
   双余量 A·eps3·|h|＋eps' 中 eps' 全称消去，A·eps3·|h| 并右端；单跳。 *)
Theorem p2t1c_T2_abs_h_sq_supply : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_abs_h_sq_le_eps A h eps3 eps' HA Hh3 Heps').
Qed.

(* ################ 二、9(f) 登记：直引收账＋语句面重述类型装配机检 ########### *)

(* f-1（盘点 #32）：real_db_breaking_bound_eps@S10:979 之 Bishop 升格面登记件。
   复合系数 D 形（inv(分区)·T·(exp·…)）：零施工登记＝CertB 具名件直引收账，
   语句面由本席逐字重述并做类型装配（下 Definition 之类型即本席重述面，
   与 p2t1b_T2_db_breaking_bound_supply 逐字不合即编译炸＝复验带响）。 *)
Definition p2t1c_T2_db_breaking_bound_reg :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s'))))))) :=
  p2t1b_T2_db_breaking_bound_supply.

(* ################ 三、交叉核验面：p2t1b 四具名件 × 本席重述语句 ############ *)
(* 类型装配 Check：右型＝本席独立重述语句，左项＝CertB 具名件。
   四发全过＝两席语句面逐字机检一致（G2 留痕）。 *)

Check (p2t1b_T2_abs_le_quad_supply :
  forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2))).

Check (p2t1b_T2_quad_t_le_h_supply :
  forall (x h eps : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx))
                          (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one)
                             real_two_pos_local) eps)
               (real_abs h))).

Check (p2t1b_T2_abs_h_sq_supply :
  forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h))).

Check (p2t1b_T2_db_breaking_bound_supply :
  forall (S0 : Type) (keep : S0 -> Set)
         (keep_dec : forall s : S0, Or (keep s) (Not (keep s)))
         (real_transition : S0 -> S0 -> Real)
         (real_transition_nonneg : forall s s' : S0,
            real_le real_zero (real_transition s s'))
         (real_transition_sym : forall s s' : S0,
            real_eq (real_transition s s') (real_transition s' s))
         (real_energy : S0 -> Real)
         (D : Real) (D_pos : real_lt real_zero D)
         (L E_max : Real)
         (real_metric : S0 -> S0 -> Real)
         (real_energy_lipschitz : forall s s' : S0,
            real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
                    (real_mult L (real_metric s s')))
         (real_energy_lower : forall s : S0,
            real_le (real_opp E_max) (real_energy s))
         (real_sum_over_S : (S0 -> Real) -> Real)
         (real_evicted_partition_pos : real_lt real_zero
            (real_evicted_partition S0 keep keep_dec real_energy D D_pos
               real_sum_over_S))
         (s s' : S0),
    keep s -> keep s' ->
    real_le_b (real_db_breaking S0 keep keep_dec real_transition real_energy
                 D D_pos real_sum_over_S real_evicted_partition_pos s s')
              (real_mult
                 (real_inv_pos (real_evicted_partition S0 keep keep_dec real_energy
                                  D D_pos real_sum_over_S)
                               real_evicted_partition_pos)
                 (real_mult (real_transition s s')
                    (real_mult (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                       (real_mult
                          (real_mult (real_mult (real_inv_pos D D_pos) L)
                                     (real_metric s s'))
                          (cauchy_real_exp
                             (real_mult (real_mult (real_inv_pos D D_pos) L)
                                        (real_metric s s')))))))).

(* ################ G3 提取探针（一人一目录 _tp2t1c_g3out；Q 层见证） ######### *)
(* 机理（A1 卡＋G1 卡）：实数层接口语句件不入提取集；见证面另立 Q 层纯函数——
   主题对位：多 eps 组合的逐点正 eps 供给族 1/(n+2)。 *)
Definition p2t1c_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1c_g3out".
Extraction "p2t1c_G3_Cert.ml" p2t1c_g3_pick.

(* ################ 收尾：文尾逐件假设面打印（G2/G3 留痕） ################### *)
Print Assumptions p2t1c_T2_abs_le_quad_supply.
Print Assumptions p2t1c_T2_quad_t_le_h_supply.
Print Assumptions p2t1c_T2_abs_h_sq_supply.
Print Assumptions p2t1c_T2_db_breaking_bound_reg.
Print Assumptions p2t1b_T2_abs_le_quad_supply.
Print Assumptions p2t1b_T2_quad_t_le_h_supply.
Print Assumptions p2t1b_T2_abs_h_sq_supply.
Print Assumptions p2t1b_T2_db_breaking_bound_supply.
