(* ============================================================ *)
(* UpAblP2T1_CertB.v —— G1 席（论文2 T 簇第二批供给席·尾簇收账＋T2 补齐）    *)
(*   论文2 T 簇合并单 28 行之尾簇领地收账件＋增配 T2 补齐申报件（新独立批件）  *)
(* 工单：attn\_ts1_论文2登记收割报告-20260920.md §四＋协调增配令（T2 并入本件）*)
(* 模板体例：UpAblP1T1_AlignCert.v／UpAblP1T2_GrpoAuditCert.v；姊妹件：      *)
(*   UpAblP2T1_Cert.v（A1 席，27/28 行，本席零触其文件）。                    *)
(* 原树零改：UpRealLeB／UpRealLeB2／S08／S09／S10 全部只读消费；              *)
(*   不入 order.txt/_CoqProject；禁触 9.0 任何产物。                          *)
(*                                                              *)
(* 【尾簇领地收账（N1 零施工登记即收）】本席领地＝合并单中不属于前三簇        *)
(*   （S06 簇/AttnDoeblin 簇/S08 簇）的 13 行：1/2/3/4/7/17/21/22/23/24/     *)
(*   T1/27(T2)/28(T3)。实测 A1 席 UpAblP2T1_Cert.v 已逐行具名覆盖（12 行：   *)
(*   p2t1_T_pos_supply…p2t1_x3d_le_b_mult_r，其四关全绿、件在盘且件新于文），*)
(*   按纪律「已证/已被既有件覆盖＝登记即收」，本席零重施工、零重复认领；      *)
(*   唯 T2（行 27）为其挂账行，增配本席。                                    *)
(*                                                              *)
(* 【T2 定谳（本席实测新获，fail-loud 勘误）】A1 挂账之「结论 9(e)/(f) 四件  *)
(*   （盘点 #24/25/28/32）可升格未建」实为漏检——续建层 UpRealLeB2.v 已全部   *)
(*   升格落盘：F.4 real_abs_le_quad_B(:403)／F.5 real_quad_t_le_h_B(:423)／  *)
(*   F.6 real_abs_h_sq_le_B(:442)／F.7 real_db_breaking_bound_B(:477，节内   *)
(*   出节 16 参)；其文件尾注自书「盘点清单显式假设四件全部升格落盘本文件」。  *)
(*   故 T2 之 S1 路线「同一闭包器族批量 Corollary 申报」按直引形兑现：本件    *)
(*   四具名供给定理逐一绑定槽坐标至在库件，非本席新证、如实申报；            *)
(*   本席增量＝①漏检勘误与四件独立复验（G4 模块核验全链假设面零）            *)
(*   ②具名证书入账③领地 13 行收账落册。                                     *)
(*                                                              *)
(* 红线自审：                                                               *)
(*  [x] 纯构造性零承认件（头注全中文，无任何英文禁词字面）                    *)
(*  [x] 语句面全 Set 层（Id/Not/Or 别名、real_lt/real_le/real_le_b/real_eq   *)
(*      Set 层谓词面；零裸命题入语句与前件位）                                *)
(*  [x] 原树零改；本件独立批件（一人一文件一人一提取目录）                     *)
(*  [x] 编译收口＋文尾逐件假设面打印全闭（G2）                                *)
(*  [x] 提取见证面取 Q 层纯函数（A1 卡机理：接口形件入提取集即交界魔数）       *)
(*  [x] 模块核验EXIT=0（G4；全链含 UpRealLeB2 四件＝T2 在库面独立复验）        *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
From Stdlib Require Import Extraction.

(* ################ T2 补齐：结论 9(e)/(f) 四具名供给（批量 Corollary 直引形） ## *)

(* T2-e-1（盘点 #24）：结论 9(e) real_abs_le_quad_eps@S08:4901 之 Bishop 升格面。
   槽形：五前件多 eps 组合（X≤eps1、−X≤2t²+eps2、三正性）；升格＝尾自由 eps
   消去、前提位原样保留（前提位改造已由在库件完成）；直引 F.4。 *)
Theorem p2t1b_T2_abs_le_quad_supply : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
               (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB HA Htwo.
  exact (real_abs_le_quad_B X t eps1 eps2 HXA HXB HA Htwo).
Qed.

(* T2-e-2（盘点 #25）：结论 9(e) real_quad_t_le_h_eps@S08 之 Bishop 升格面。
   余量内嵌 |h| 因子随固定端并入右端；eps' 全称余量消去；直引 F.5。 *)
Theorem p2t1b_T2_quad_t_le_h_supply : forall (x h eps : Real)
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
  exact (real_quad_t_le_h_B x h eps Hx Hh Heps).
Qed.

(* T2-e-3（盘点 #28）：结论 9(e) real_abs_h_sq_le_eps@S09:1087 之 Bishop 升格面。
   双余量 A·eps3·|h| + eps'，eps' 消去；直引 F.6。 *)
Theorem p2t1b_T2_abs_h_sq_supply : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  exact (real_abs_h_sq_le_B A h eps3 HA Hh3).
Qed.

(* T2-f-1（盘点 #32）：结论 9(f) real_db_breaking_bound_eps@S10:979 之 Bishop
   升格面。复合系数 D 形：完成器取非负系数版（F.1 器；C:=invZ·T·(exp+1) 仅
   非负），eps 与 eps' 同时消去；出节 16 参逐字镜像（Check 探针实测签名）；
   直引 F.7。 *)
Theorem p2t1b_T2_db_breaking_bound_supply :
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
                                        (real_metric s s'))))))).
Proof.
  intros S0 keep keep_dec real_transition real_transition_nonneg
         real_transition_sym real_energy D D_pos L E_max real_metric
         real_energy_lipschitz real_energy_lower real_sum_over_S
         real_evicted_partition_pos s s' Hs Hs'.
  exact (real_db_breaking_bound_B S0 keep keep_dec real_transition
           real_transition_nonneg real_transition_sym real_energy D D_pos
           L E_max real_metric real_energy_lipschitz real_energy_lower
           real_sum_over_S real_evicted_partition_pos s s' Hs Hs').
Qed.

(* ################ G3 提取探针（一人一目录 _tp2t1b_g3out；Q 层纯函数见证） #### *)
(* 机理（A1 卡＋Y2 卡）：接口形件入提取集即 Caml 交界魔数——本件供给定理全为   *)
(* 实数层接口语句，不入提取集；见证面另立 Q 层纯函数。 *)
Definition p2t1b_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1b_g3out".
Extraction "p2t1b_G3_Cert.ml" p2t1b_g3_pick.

(* ################ 收尾：文尾逐件假设面打印（G2 留痕） ################ *)
Print Assumptions p2t1b_T2_abs_le_quad_supply.
Print Assumptions p2t1b_T2_quad_t_le_h_supply.
Print Assumptions p2t1b_T2_abs_h_sq_supply.
Print Assumptions p2t1b_T2_db_breaking_bound_supply.
