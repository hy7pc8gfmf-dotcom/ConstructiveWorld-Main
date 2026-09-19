(* ============================================================ *)
(* UpAblT13c_G13.v —— 消融清欠席 T13c（批9 三路+G13 Id 束）G13 位件        *)
(* 辖区（T13a-2 勘误与 T13b-3/D4 挂账移交，逐位现档坐标）：                 *)
(*   位1 G13_EvictFam.v:61  Z_thermo_pos（UpEvictId Id 层）                 *)
(*        → 单点 SumOver 包 discharge（exp_neg_pos 直喂）                  *)
(*   位2 G13_EvictFam.v:68  transition_normalization（UpEvictId Id 层）     *)
(*        → 常值一核 supply（单点世界行和=该行本身=1）                     *)
(*   位3 G13_EvictFam.v:71  detailed_balance（UpEvictId Id 层）            *)
(*        → 源核缩放族 t(s,s')=dist(s')·c supply（assoc-comm 纯代数；      *)
(*          非循环——普查依据 :120 消费 :71 Variable 本体，禁直喂已定谳）    *)
(*   位4 G13_EvictFam.v:87  evicted_partition_pos（UpEvictId Id 层）        *)
(*        → 全保留判定 inl tt 供形+exp_neg_pos                            *)
(*   位5 G13_EvictFam.v:464 transition_normalization（EvictIdReq req 层）   *)
(*        → 两点世界行归一核 supply（half+half==one 纯接口代数链）          *)
(*   位6 G13_EvictFam.v:468 detailed_balance（EvictIdReq req 层）           *)
(*        → 源核缩放族 supply（配分正性由两点正和 discharge，零数据槽）     *)
(* 最小 SumOver 实例构造（T13b D4 挂账工单兑现；照 T7b 两点包先例最小化）： *)
(*   全库 SumOver Class@S01:1398 零具体 Instance，abs_sum_le 字段系 W1 墙   *)
(*   在两点/任意多点载体不可满足；单点状态空间上八字段全退化可构造          *)
(*   （abs_sum_le 退化为 le_refl）——uab_ssUnit+uab_soUnit 即最小 SumOver   *)
(*   实例世界，G13 UpEvictId {RI}{SS}{SO} 三 Context 束自此可实例化。       *)
(* 消融形（诚实申报）：全部定理对抽象载体全参（Id 层 {RI} 全参、req 层      *)
(*   {R}{RIS} 全参），零具体实例依赖、零装配桥、零数据槽隐藏；位6 配分正性  *)
(*   由两点正和 discharge（plus_positive+exp_neg_pos），非显式参。          *)
(* 分级：位1/2/4/5 = N3（实例供给）；位3/6 = N3（实例供给·核族构造）。      *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、G13_EvictFam。    *)
(* 四关留痕：Live_X/attn/logs/g{0..4}-UpAblT13c_*                         *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import G13_EvictFam.

(* ======== 一、Id 层：单点 SumOver 包（最小 SumOver 实例世界） ======== *)

Lemma uab_unit_unique : forall a b : unit, Id a b.
Proof.
  intros a b.
  destruct a, b.
  reflexivity.
Qed.

Definition uab_ssUnit {RI : RealInterface} : StateSpace RI :=
  {| S := unit;
     szero := tt;
     splus := fun _ _ => tt;
     smult := fun _ _ => tt;
     sopp := fun _ => tt;
     splus_assoc := fun _ _ _ => id_refl;
     splus_comm := fun _ _ => id_refl;
     splus_zero := fun a => uab_unit_unique tt a;
     splus_opp := fun _ => id_refl;
     smult_one := fun a => uab_unit_unique tt a;
     smult_assoc := fun _ _ _ => id_refl;
     smult_distrib_r := fun _ _ _ => id_refl;
     smult_distrib_l := fun _ _ _ => id_refl;
     smetric := fun _ _ => zero;
     smetric_sym := fun _ _ => id_refl;
     smetric_pos := fun _ _ => le_refl zero;
     smetric_zero := fun a b _ => uab_unit_unique a b;
     smetric_triangle :=
       fun _ _ _ => le_id_r zero zero (plus zero zero) (id_sym (plus_zero zero)) (le_refl zero);
     clim := fun _ _ => unit;
     clim_unique := fun _ l1 l2 _ _ => uab_unit_unique l1 l2;
     cauchy_complete_S := fun _ _ => existT (fun _ : unit => unit) tt tt |}.

Lemma uab_ssUnit_elem {RI : RealInterface} : @S RI uab_ssUnit.
Proof.
  unfold uab_ssUnit.
  exact tt.
Defined.

Definition uab_soUnit {RI : RealInterface} : SumOver RI (@uab_ssUnit RI) :=
  {| sum_over_S := fun f => f uab_ssUnit_elem;
     sum_over_S_linear := fun a f => (@id_refl _ (mult a (f uab_ssUnit_elem)));
     sum_over_S_add := fun f g => (@id_refl _ (plus (f uab_ssUnit_elem) (g uab_ssUnit_elem)));
     sum_over_S_ext := fun f g H => H uab_ssUnit_elem;
     sum_over_S_le := fun f g H => H uab_ssUnit_elem;
     sum_over_S_nonneg := fun f H => H uab_ssUnit_elem;
     sum_over_S_zero_nonneg := fun f _ H0 s =>
       (match s as x return (Id (f x) zero) with
        | tt => H0
        end);
     abs_sum_le := fun f => le_refl (abs (f uab_ssUnit_elem)) |}.

(* ---- 交换核族引理（Id 层·任意载体）：p(s)·(p(s')·c) == p(s')·(p(s)·c) ---- *)
Lemma uabT13c_swap_id_gen :
  forall (A : Set) {RI : RealInterface} (p : A -> @R RI) (c : @R RI) (s s' : A),
    Id (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros A RI p c s s'.
  apply (id_trans (mult_assoc (p s) (p s') c)).
  apply (id_trans (id_cong (fun x : @R RI => mult x c) (mult_comm (p s) (p s')))).
  exact (id_sym (mult_assoc (p s') (p s) c)).
Qed.

(* ---- 位1 ←G13:61（配分正性 discharge：单点和=因子行，exp_neg_pos 直喂） ---- *)
Theorem uabT13c_evict61 :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : lt zero D) (energy : @S RI uab_ssUnit -> @R RI),
    lt zero (@evict_Z_thermo RI uab_ssUnit uab_soUnit D D_pos energy).
Proof.
  intros RI D D_pos energy.
  unfold evict_Z_thermo, evict_boltzmann_factor, sum_over_S.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy uab_ssUnit_elem))).
Qed.

(* ---- 位4 ←G13:87（逐出配分正性：全保留判定供形，分支 iota 后同位1） ---- *)
Theorem uabT13c_evict87 :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : lt zero D) (energy : @S RI uab_ssUnit -> @R RI),
    lt zero (@evict_evicted_partition RI uab_ssUnit uab_soUnit D D_pos energy
               (fun _ : @S RI uab_ssUnit => unit)
               (fun _ : @S RI uab_ssUnit => inl tt : Or unit (Not unit))).
Proof.
  intros RI D D_pos energy.
  unfold evict_evicted_partition, evict_boltzmann_factor, sum_over_S.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy uab_ssUnit_elem))).
Qed.

(* ---- 位2 ←G13:68（行归一 discharge：常值一核，单点和=行=1） ---- *)
Theorem uabT13c_evict68 :
  forall {RI : RealInterfaceEnhanced} (s : @S RI uab_ssUnit),
    Id (@sum_over_S RI uab_ssUnit uab_soUnit (fun s' : @S RI uab_ssUnit => one)) one.
Proof.
  intros RI s.
  exact id_refl.
Qed.

(* ---- 位3 ←G13:71（详细平衡 discharge：源核缩放族 t(s,s')=dist(s')·c；
        配分正性由位1 discharge，零数据槽；单点世界为最小实例面） ---- *)
Theorem uabT13c_evict71 :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : lt zero D) (energy : @S RI uab_ssUnit -> @R RI) (c : @R RI),
    forall s s' : @S RI uab_ssUnit,
      Id (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                  (uabT13c_evict61 D D_pos energy) s)
               (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                        (uabT13c_evict61 D D_pos energy) s') c))
         (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                  (uabT13c_evict61 D D_pos energy) s')
               (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                        (uabT13c_evict61 D D_pos energy) s) c)).
Proof.
  intros RI D D_pos energy c s s'.
  exact (uabT13c_swap_id_gen (@S RI uab_ssUnit)
           (fun x : @S RI uab_ssUnit =>
              @evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                (uabT13c_evict61 D D_pos energy) x)
           c s s').
Qed.

(* ======== 二、req 层：两点供给世界（{R}{RIS} 全参，零桥零数据槽） ======== *)
Import RealInterfaceEnhancedMod.

Section UabT13cG13Req.

Context {R0 : Set} {RIS0 : RealInterfaceEnhancedSetoid R0}.

Definition uab_t2sum (f : bool -> R0) : R0 := plus (f true) (f false).

Definition uab_half : R0 :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* ---- 交换核族引理（req 层·两点载体） ---- *)
Lemma uabT13c_swap_req_gen :
  forall (p : bool -> R0) (c : R0) (s s' : bool),
    req (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros p c s s'.
  exact (req_trans (mult (p s) (mult (p s') c))
                   (mult (mult (p s) (p s')) c)
                   (mult (p s') (mult (p s) c))
                   (mult_assoc (p s) (p s') c)
                   (req_trans (mult (mult (p s) (p s')) c)
                              (mult (mult (p s') (p s)) c)
                              (mult (p s') (mult (p s) c))
                              (req_mult_compat (mult (p s) (p s')) (mult (p s') (p s)) c c
                                               (mult_comm (p s) (p s')) (req_refl c))
                              (req_sym (mult (p s') (mult (p s) c))
                                       (mult (mult (p s') (p s)) c)
                                       (mult_assoc (p s') (p s) c)))).
Qed.

(* 两点行归一代数核：half+half == one *)
Lemma uabT13c_half_row : req (plus uab_half uab_half) one.
Proof.
  unfold uab_half.
  assert (H1 : req (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                   (inv_pos (plus one one) (plus_positive one one one_pos one_pos))).
  { exact (req_trans (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))
                     (mult_comm one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult_one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))). }
  assert (HDL : req (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                    (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                          (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))).
  { exact (req_trans (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                     (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                     (mult_comm (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (req_trans (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                                (plus (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one))
                                (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                (distrib (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one one)
                                (req_plus_compat (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)))). }
  exact (req_trans (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) one
                   (req_trans (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                              (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                              (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                              (req_plus_compat (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                               (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1)
                                               (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1))
                              (req_sym (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                       (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                       HDL))
                   (inv_pos_correct (plus one one) (plus_positive one one one_pos one_pos))).
Qed.

(* ---- 位5 ←G13:464（行归一 discharge：两点一致核，行和=half+half=one） ---- *)
Theorem uabT13c_evq_norm464 :
  forall s : bool,
    req (uab_t2sum (fun s' : bool => uab_half)) one.
Proof.
  intro s.
  unfold uab_t2sum.
  exact uabT13c_half_row.
Qed.

(* ---- 两点配分正性（位6 的 Z_thermo_pos 供形：逐点 exp_neg_pos+两点正和） -- *)
Theorem uabT13c_evq_Zpos2 :
  forall (D : R0) (D_pos : lt zero D) (energy : bool -> R0),
    lt zero (@evq_Z_thermo R0 RIS0 bool uab_t2sum D D_pos energy).
Proof.
  intros D D_pos energy.
  unfold evq_Z_thermo, uab_t2sum, evq_boltzmann_factor.
  exact (plus_positive (exp_neg (mult (inv_pos D D_pos) (energy true)))
                       (exp_neg (mult (inv_pos D D_pos) (energy false)))
                       (exp_neg_pos (mult (inv_pos D D_pos) (energy true)))
                       (exp_neg_pos (mult (inv_pos D D_pos) (energy false)))).
Qed.

(* ---- 位6 ←G13:468（详细平衡 discharge：源核缩放族 t(s,s')=dist(s')·c；
        两点正和 discharge 配分正性，零数据槽） ---- *)
Theorem uabT13c_evq_db468 :
  forall (D : R0) (D_pos : lt zero D) (energy : bool -> R0) (c : R0),
    forall s s' : bool,
      req (mult (@evq_boltzmann_dist_attn R0 RIS0 bool uab_t2sum D D_pos energy
                   (uabT13c_evq_Zpos2 D D_pos energy) s)
                (mult (@evq_boltzmann_dist_attn R0 RIS0 bool uab_t2sum D D_pos energy
                         (uabT13c_evq_Zpos2 D D_pos energy) s') c))
          (mult (@evq_boltzmann_dist_attn R0 RIS0 bool uab_t2sum D D_pos energy
                   (uabT13c_evq_Zpos2 D D_pos energy) s')
                (mult (@evq_boltzmann_dist_attn R0 RIS0 bool uab_t2sum D D_pos energy
                         (uabT13c_evq_Zpos2 D D_pos energy) s) c)).
Proof.
  intros D D_pos energy c s s'.
  exact (uabT13c_swap_req_gen
           (fun x : bool =>
              @evq_boltzmann_dist_attn R0 RIS0 bool uab_t2sum D D_pos energy
                (uabT13c_evq_Zpos2 D D_pos energy) x)
           c s s').
Qed.

End UabT13cG13Req.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13c_evict61.
Print Assumptions uabT13c_evict87.
Print Assumptions uabT13c_evict68.
Print Assumptions uabT13c_evict71.
Print Assumptions uabT13c_evq_norm464.
Print Assumptions uabT13c_evq_db468.
