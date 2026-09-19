(* ============================================================ *)
(* UpAblD1S14_UpReqCauchy.v —— FA-D1S14 论文域消融施工席·UpReqCauchy 余量包 *)
(* 席位：FA-D1S14（包装协议 v2 内嵌执行）｜独立伴生件·原树零改·零 git            *)
(*                                                              *)
(* 辖区：UpReqCauchy.v（1508 行，md5 f5333502c49d3f0457dd4dfe22916f2c，         *)
(*   Live_X 副本与 ConstructiveWorld-Main 正册同值，开工实测零代际漂移）         *)
(*   32 有效位中 S11 件头认领 20 槽＋RN:134 条件形（其供给定理全称量化携带）、      *)
(*   D1-① 已切 lt_plus_compat_lt_le/le_lt:123/124、S2 已切 log_lt_mono_cc:822、  *)
(*   幻影 L133——本件施工 S11 件头挂账移交的真余量 7 槽：                         *)
(*   strict_concavity:101｜strong_concavity:1121｜entropy_tangent:1386｜         *)
(*   r_arch_pow:224｜lim_metric_approx:986（五槽无条件供给）                     *)
(*   metric_triangle_plain:135｜le_all_eps_zero:990（两槽诚实条件形，全称前提位） *)
(*   weak_trich:1432（W 墙照登记；本件附可分离的具体实例绕行直喂节，S12           *)
(*   token_eq_dec:=bool 同款——real_weak_trich@S07:5719 已完整证明，S07 原注      *)
(*   勘误「弱三分不可证需 Markov」记录有误，母本 L1431 注释亦自述 Real 层可满足；  *)
(*   普查 W#1 勘误候选如实入账，墙本体仍按墙登记簇处置）                          *)
(*                                                              *)
(* 供给底座（全部现档实测）：opp_lt_compat/req_plus_compat/plus_comm/plus_zero/   *)
(*   mult_comm/mult_one/mult_zero/lt_le_iff/le_refl＝接口字段（S07:7915-8020 区）； *)
(*   real_opp_proj@S02:1316｜real_plus_proj@S02:1304｜real_abs_proj@S03:6544｜    *)
(*   real_lt_abs_bound/q_abs_lt_two_sided@S02:903/926｜real_weak_trich@S07:5719｜ *)
(*   r_arch_pow_real@CW220:1032（N1 直喂）｜NatLe_lift/NatLe_drop@S01:120/111。    *)
(*   metric δ 同体 real_metric := real_abs(real_plus x (real_opp y))（S03:6526）。*)
(*                                                              *)
(* 分级（禁注水如实申报）：无条件 5 槽＝A1/A2 一行直配＋req 链、A3 mult/plus 零链、  *)
(*   A4 N1 直喂＋rpow 镜像 δ 同体、A5 lim+metric eps-N 语义链（本批唯一实质内容腿）； *)
(*   条件形 2 槽＝plain Or 形序无消去深水（母本 L126-133 自述，S8 r_max_le_r_plain  *)
(*   同判例），全称前提位入包，PA 照样 Closed（S13 uac_gibbs 同款）；               *)
(*   绕行 1 槽＝W 墙登记＋实例直喂（可分离节，整体摘除不伤他槽）。                  *)
(* 形态：S11/S13 单点实例供给申报形（逐槽独立供给定理，实例指派见各节头注）；        *)
(*   语句面全 Set 层（接口 Set 层 Or/Not，S01:66-68），零新增公理面。              *)
(* 依赖：CW_ConstructiveWorld_219／UpReqAlgebra／CW220_Extensions（只读消费）；    *)
(*   零 Require 槽位母本（防混代际坑）、零 git、零注册面、论文目录不碰。           *)
(* 四关留痕：Live_X/attn/logs/g{1,2,3,4}-UpAblD1S14_*.{log,exit}                 *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import CW220_Extensions.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Import RealInterfaceEnhancedMod.
Open Scope Q_scope.

(* ============ 供给底座（本件自持辅件，uabd1s14_ 前缀防撞） ============ *)

(* opp(opp x) req x（real_eq 逐 eps 形；real_opp_proj@S02:1316 两次投影） *)
Lemma uabd1s14_cau_opp_opp : forall x : Real, req (opp (opp x)) x.
Proof.
  intros x.
  change (real_eq (opp (opp x)) x).
  apply real_eq_of_zero_diff.
  intro n.
  assert (H1 : projT1 (opp (opp x)) n == - projT1 (opp x) n)
    by exact (real_opp_proj (real_opp x) n).
  assert (H2 : projT1 (opp x) n == - projT1 x n)
    by exact (real_opp_proj x n).
  rewrite H1. rewrite H2.
  rewrite (Qopp_involutive (projT1 x n)).
  ring.
Qed.

(* half := inv_pos(1+1)（req_half_pos@UpReqAlgebra:308 同款见证） *)
Definition uabd1s14_cau_half :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* kappa 槽实例：κ := exp_neg half（κ_pos/κ<1 两腿皆接口字段直配，S11 同款） *)
Definition uabd1s14_cau_kappa := exp_neg uabd1s14_cau_half.

(* 母本节内 Fixpoint req_r_pow（L215-219）镜像：δ 同体（one/mult 投影同体） *)
Fixpoint uabd1s14_cau_rpow (x : Real) (n : nat) : Real :=
  match n with
  | O => one
  | Datatypes.S m => mult x (uabd1s14_cau_rpow x m)
  end.

(* ============ A1 槽 strict_concavity:101（实例 entropy_gradient := opp） ============ *)
(* 母本语句：forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x) *)
Theorem uabd1s14_cau_strict_concavity_supply :
  forall x y : Real, lt x y -> lt (opp y) (opp x).
Proof.
  intros x y H.
  exact (opp_lt_compat x y H).
Qed.

(* ============ A2 槽 strong_concavity:1121（实例 mu := one，entropy_gradient := opp） ============ *)
(* 母本语句：forall x y : R, lt x y -> le (mult mu (req_minus y x))                *)
(*   (req_minus (entropy_gradient x) (entropy_gradient y))                        *)
Theorem uabd1s14_cau_strong_concavity_supply :
  forall x y : Real,
    le (mult one (req_minus y x)) (req_minus (opp x) (opp y)).
Proof.
  intros x y.
  apply (lt_le_iff _ _). right.
  unfold req_minus.
  apply (req_trans (mult one (plus y (opp x))) (plus y (opp x))
                   (plus (opp x) (opp (opp y)))).
  - apply (req_trans (mult one (plus y (opp x)))
                     (mult (plus y (opp x)) one) (plus y (opp x))).
    + apply mult_comm.
    + apply mult_one.
  - apply (req_sym (plus (opp x) (opp (opp y))) (plus y (opp x))).
    apply (req_trans (plus (opp x) (opp (opp y))) (plus (opp x) y)
                     (plus y (opp x))).
    + apply (req_plus_compat (opp x) (opp x) (opp (opp y)) y).
      * apply (req_refl (opp x)).
      * exact (uabd1s14_cau_opp_opp y).
    + apply plus_comm.
Qed.

(* ============ A3 槽 entropy_tangent:1386（实例 entropy := 零函数，entropy_gradient := 零函数） ============ *)
(* 母本语句：forall x y : R,                                                     *)
(*   le (entropy y) (plus (entropy x) (mult (entropy_gradient x) (req_minus y x))) *)
Theorem uabd1s14_cau_entropy_tangent_supply :
  forall x y : Real,
    le zero (plus zero (mult zero (req_minus y x))).
Proof.
  intros x y.
  apply (lt_le_iff _ _). right.
  unfold req_minus.
  apply (req_sym (plus zero (mult zero (plus y (opp x)))) zero).
  apply (req_trans (plus zero (mult zero (plus y (opp x))))
                   (mult zero (plus y (opp x))) zero).
  - apply (req_trans (plus zero (mult zero (plus y (opp x))))
                     (plus (mult zero (plus y (opp x))) zero)
                     (mult zero (plus y (opp x)))).
    + apply plus_comm.
    + apply plus_zero.
  - apply (req_trans (mult zero (plus y (opp x)))
                     (mult (plus y (opp x)) zero) zero).
    + apply mult_comm.
    + apply mult_zero.
Qed.

(* ============ A4 槽 r_arch_pow:224（实例 kappa := exp_neg half；N1 直喂 CW220:1032） ============ *)
(* 母本语句：forall (a : R), lt zero a -> forall eps : R, lt zero eps ->           *)
(*   sigT (fun n : nat => lt (mult a (req_r_pow kappa n)) eps)                    *)
Theorem uabd1s14_cau_r_arch_pow_supply :
  forall (a : Real), lt zero a ->
    forall eps : Real, lt zero eps ->
    sigT (fun n : nat =>
      lt (mult a (uabd1s14_cau_rpow uabd1s14_cau_kappa n)) eps).
Proof.
  intros a Ha eps Heps.
  assert (Hk1 : lt zero uabd1s14_cau_kappa).
  { apply exp_neg_pos. }
  assert (Hk2 : lt uabd1s14_cau_kappa one).
  { apply (lt_id_r (exp_neg uabd1s14_cau_half) (exp_neg zero) one).
    - apply exp_neg_zero.
    - apply (exp_neg_decr zero uabd1s14_cau_half).
      apply inv_pos_pos. }
  exact (BudgetReal.r_arch_pow_real uabd1s14_cau_kappa Hk1 Hk2 a Ha eps Heps).
Qed.

(* ============ A5 槽 lim_metric_approx:986（lim+metric eps-N 语义链，本批实质内容腿） ============ *)
(* 母本语句：forall (u : nat -> R) (l : R), lim u l -> forall eps : R, lt zero eps -> *)
(*   sigT (fun N : nat => forall n : nat, NatLe N n -> lt (metric (u n) l) eps)    *)
Theorem uabd1s14_cau_lim_metric_supply :
  forall (u : nat -> Real) (l : Real), lim u l ->
    forall eps : Real, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      lt (metric (u n) l) eps).
Proof.
  intros u l Hu eps Heps.
  destruct Heps as [e0 [He0 [Ne HNe]]].
  (* e0/4 与 e0/2 的 Q 正性（real_weak_trich@S07:5719 的 eps/3 分割同款） *)
  assert (He0' : 0 < e0) by (apply QltT_to_Qlt; exact He0).
  assert (Hq4 : QltT 0 (e0 * (1#4)%Q)) by (apply Qlt_to_QltT; lra).
  assert (Hq2 : QltT 0 (e0 * (1#2)%Q)) by (apply Qlt_to_QltT; lra).
  destruct (Hu (e0 * (1#4)%Q) Hq4) as [N1 HN1].
  exists (Nat.max N1 Ne).
  intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift.
    apply Nat.le_trans with (Nat.max N1 Ne).
    - apply Nat.le_max_l.
    - apply NatLe_drop. exact Hn. }
  assert (Hne : NatLe Ne n).
  { apply NatLe_lift.
    apply Nat.le_trans with (Nat.max N1 Ne).
    - apply Nat.le_max_r.
    - apply NatLe_drop. exact Hn. }
  destruct (HN1 n (NatLe_drop _ _ Hn1)) as [Hup Hdn].
  (* real_lt_abs_bound@S02:926：双向夹逼 ⟹ 逐点 Qabs 界（对固定 n，m 尾段） *)
  destruct (real_lt_abs_bound u l (e0 * (1#4)%Q) Hq4 N1
              (fun m Hm => HN1 m Hm) n
              (NatLe_drop _ _ Hn1)) as [M HM].
  (* metric 投影 δ/ι 同体：projT1 (metric (u n) l) m ≡ Qabs (projT1 (u n) m - projT1 l m) *)
  exists (e0 * (1#2)%Q). split.
  - exact Hq2.
  - exists (Nat.max M Ne). intros m Hm.
    assert (Hsmall : QltT (Qabs (projT1 (u n) m - projT1 l m)) (e0 / 4)).
    { apply HM. apply Nat.le_trans with (Nat.max M Ne).
      - apply Nat.le_max_l.
      - apply NatLe_drop. exact Hm. }
    assert (Hepsm : QltT e0 (projT1 eps m - projT1 zero m)).
    { apply HNe. apply NatLe_lift.
      apply Nat.le_trans with (Nat.max M Ne).
      - apply Nat.le_max_r.
      - apply NatLe_drop. exact Hm. }
    assert (Hzm : projT1 zero m == 0) by apply Qeq_refl.
    (* metric 投影 δ 逐引理链（S07:6711 setoid_rewrite 同款） *)
    assert (Habs : projT1 (metric (u n) l) m == Qabs (projT1 (u n) m - projT1 l m)).
    { cbv beta iota delta [metric real_metric].
      rewrite (real_abs_proj (real_plus (u n) (real_opp l)) m).
      rewrite (real_plus_proj (u n) (real_opp l) m).
      rewrite (real_opp_proj l m).
      apply Qabs_wd. ring. }
    apply Qlt_to_QltT.
    setoid_rewrite Habs.
    remember (Qabs (projT1 (u n) m - projT1 l m)) as xa.
    assert (Hsmall' : xa < e0 * (1#4)%Q)
      by (apply QltT_to_Qlt; exact Hsmall).
    assert (Hepsm' : e0 < projT1 eps m - 0)
      by (apply QltT_to_Qlt; exact Hepsm).
    lra.
Qed.

(* ============ B 槽组·诚实条件形（全称前提位入包，S13 uac_gibbs 同款） ============ *)
(* metric_triangle_plain:135 与 le_all_eps_zero:990：结论为 plain Or 形序谓词，     *)
(* 抽象接口由 eps 形不可消去导出（母本 L126-133 头注自述「序无消去」；S8             *)
(* r_max_le_r_plain 同判例；concrete 层 real_le 为 Or(lt,eq) 两支需符号判定，        *)
(* 实测不可由现有底座机械构造）——按诚实打包形以全称前提位承载，登记不虚报无条件供给。 *)
Inductive uabd1s14_cau_cond_pack2 : Type :=
| uabd1s14_cau_cond_pack2_intro :
    (forall a b c : Real,
       le (metric a c) (plus (metric a b) (metric b c))) ->
    (forall x : Real,
       (forall eps : Real, lt zero eps -> lt x eps) -> le x zero) ->
    uabd1s14_cau_cond_pack2.

Theorem uabd1s14_cau_cond_pack2_supplied :
  (forall a b c : Real,
     le (metric a c) (plus (metric a b) (metric b c))) ->
  (forall x : Real,
     (forall eps : Real, lt zero eps -> lt x eps) -> le x zero) ->
  uabd1s14_cau_cond_pack2.
Proof.
  intros H1 H2.
  exact (uabd1s14_cau_cond_pack2_intro H1 H2).
Qed.

(* ============ C 槽 weak_trich:1432（W 墙照登记＋可分离实例绕行直喂节） ============ *)
(* 墙登记照旧：抽象接口内不可导出（普查 W#1 三分律族）。本节为具体实例绕行：          *)
(* real_weak_trich@S07:5719 为完整证明引理（Qed；S07 原注勘误「需 Markov」记录有误）， *)
(* req 在 Real 实例 δ 同体 real_eq——一行直喂，零新机器。本节整体摘除不伤他槽。        *)
Theorem uabd1s14_cau_weak_trich_supply :
  forall x y : Real, Not (lt x y) -> Not (lt y x) -> req x y.
Proof.
  intros x y H1 H2.
  exact (real_weak_trich x y H1 H2).
Qed.

(* ============ 假设面收口申报 ============ *)

Print Assumptions uabd1s14_cau_opp_opp.
Print Assumptions uabd1s14_cau_strict_concavity_supply.
Print Assumptions uabd1s14_cau_strong_concavity_supply.
Print Assumptions uabd1s14_cau_entropy_tangent_supply.
Print Assumptions uabd1s14_cau_r_arch_pow_supply.
Print Assumptions uabd1s14_cau_lim_metric_supply.
Print Assumptions uabd1s14_cau_cond_pack2_supplied.
Print Assumptions uabd1s14_cau_weak_trich_supply.
