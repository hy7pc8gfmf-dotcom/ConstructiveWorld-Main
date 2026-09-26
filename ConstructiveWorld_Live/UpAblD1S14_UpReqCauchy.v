(* ============================================================ *)
(* UpAblD1S14_UpReqCauchy.v —— UpReqCauchy 待供给语句的实例供给件        *)
(*   数学使命：为源模块八条待供给语句在具体 Real 实例上给出显式供给。       *)
(* ============================================================ *)
(* 【使命】源模块 UpReqCauchy 以接口参数化方式陈述其语句；本件承接其中八条： *)
(*   五条无条件供给——strict_concavity（熵梯度的严格单调反转）、           *)
(*   strong_concavity（强凹性，取 mu:=one）、entropy_tangent（零函数的    *)
(*   切线不等式）、r_arch_pow（几何衰减的阿基米德性质，kappa:=exp_neg     *)
(*   half）、lim_metric_approx（极限的距离 ε-N 刻画，本件唯一含实质构造   *)
(*   的供给）；两条条件形——metric_triangle_plain 与 le_all_eps_zero      *)
(*   （结论为 plain Or 形序谓词，见 §B 注记）；weak_trich 附具体实例供给（见 §C 注记）。 *)
(* 【依赖】CW_ConstructiveWorld_219 / UpReqAlgebra / CW220_Extensions；   *)
(*   Stdlib：QArith / QArith.Qabs / Setoid / Morphisms / Arith / Lia /    *)
(*   Lqa。源模块仅以接口参数只读引用，不 Require 其实现文件。               *)
(* 【对标】数学原型：阿基米德性质、极限的距离刻画（ε-N）与熵函数的       *)
(*   凹性不等式；mathlib/stdlib 无直接构造实数对应物。                    *)
(* 【构造性注记】语句面全 Set 层（接口的 Or/Not 亦 Set 层）；全件 Qed     *)
(*   闭合、零承认词面、零新增公理面；两条条件供给以全称前提显式承载，    *)
(*   如实申报为条件形，Print Assumptions 仍全 Closed。文末对八条结论     *)
(*   逐一 Print Assumptions，以全部 Closed 为零外部未证假设的判据。       *)
(* 【编译配方】Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard       *)
(*   包裹限载；输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。  *)
(* 【结构总览】供给基础辅件（uabd1s14_cau_opp_opp/uabd1s14_cau_half/       *)
(*   uabd1s14_cau_kappa/uabd1s14_cau_rpow 等自持辅件）；                 *)
(*   §A1 strict_concavity 供给（实例 entropy_gradient:=opp，由           *)
(*   opp_lt_compat 直接推得）；§A2 strong_concavity 供给（实例 mu:=one，  *)
(*   mult/plus 代数链）；§A3 entropy_tangent 供给（零函数实例，          *)
(*   mult_zero 链）；§A4 r_arch_pow 供给（kappa:=exp_neg half，由        *)
(*   r_arch_pow_real（CW220_Extensions）直接推得）；§A5 lim_metric_approx *)
(*   供给（ε-N 论证链：Q 正性分割、real_lt_abs_bound 夹逼、metric 投影   *)
(*   展开）；§B 条件形组（metric_triangle_plain/le_all_eps_zero：plain    *)
(*   Or 形序谓词不可由逐 eps 形消去，以全称前提显式承载）；§C weak_trich  *)
(*   具体实例供给（real_weak_trich 为已证引理，弱三分在 Real 实例上      *)
(*   成立；抽象接口内不可导出，本节可独立移除）；假设审计区。             *)
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

(* ============ 供给基础辅件（本件自持） ============ *)

(* opp(opp x) == x（对逐 eps 的 real_eq；经 real_opp_proj 两次投影） *)
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

(* half := inv_pos(1+1)（正性见证同 req_half_pos，UpReqAlgebra） *)
Definition uabd1s14_cau_half :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* kappa 实例：κ := exp_neg half（κ>0 与 κ<1 均由接口字段直接推得） *)
Definition uabd1s14_cau_kappa := exp_neg uabd1s14_cau_half.

(* 幂函数副本：与源模块节内 Fixpoint req_r_pow 逐层展开相同（one/mult 相同） *)
Fixpoint uabd1s14_cau_rpow (x : Real) (n : nat) : Real :=
  match n with
  | O => one
  | Datatypes.S m => mult x (uabd1s14_cau_rpow x m)
  end.

(* ============ §A1 · strict_concavity 供给（实例 entropy_gradient := opp） ============ *)
(* 源模块语句：forall x y : R, lt x y -> lt (entropy_gradient y) (entropy_gradient x) *)
Theorem uabd1s14_cau_strict_concavity_supply :
  forall x y : Real, lt x y -> lt (opp y) (opp x).
Proof.
  intros x y H.
  exact (opp_lt_compat x y H).
Qed.

(* ============ §A2 · strong_concavity 供给（实例 mu := one，entropy_gradient := opp） ============ *)
(* 源模块语句：forall x y : R, lt x y -> le (mult mu (req_minus y x))                *)
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

(* ============ §A3 · entropy_tangent 供给（实例 entropy := 零函数，entropy_gradient := 零函数） ============ *)
(* 源模块语句：forall x y : R,                                                     *)
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

(* ============ §A4 · r_arch_pow 供给（实例 kappa := exp_neg half） ============ *)
(* 源模块语句：forall (a : R), lt zero a -> forall eps : R, lt zero eps ->           *)
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

(* ============ §A5 · lim_metric_approx 供给（ε-N 论证链，本件唯一实质构造） ============ *)
(* 源模块语句：forall (u : nat -> R) (l : R), lim u l -> forall eps : R, lt zero eps -> *)
(*   sigT (fun N : nat => forall n : nat, NatLe N n -> lt (metric (u n) l) eps)    *)
Theorem uabd1s14_cau_lim_metric_supply :
  forall (u : nat -> Real) (l : Real), lim u l ->
    forall eps : Real, lt zero eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      lt (metric (u n) l) eps).
Proof.
  intros u l Hu eps Heps.
  destruct Heps as [e0 [He0 [Ne HNe]]].
  (* e0/4 与 e0/2 的 Q 正性（正数乘正有理数的正性） *)
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
  (* real_lt_abs_bound：双向夹逼 ⟹ 逐点 Qabs 界（对固定 n，取 m 尾段） *)
  destruct (real_lt_abs_bound u l (e0 * (1#4)%Q) Hq4 N1
              (fun m Hm => HN1 m Hm) n
              (NatLe_drop _ _ Hn1)) as [M HM].
  (* metric 的投影展开：projT1 (metric (u n) l) m ≡ Qabs (projT1 (u n) m - projT1 l m) *)
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
    (* metric 投影展开的逐引理链 *)
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

(* ============ §B · 条件形组（结论以全称前提显式承载） ============ *)
(* metric_triangle_plain 与 le_all_eps_zero：结论为 plain Or 形序谓词，             *)
(* 无法由逐 eps 形消去导出（源模块头注自述「序无消去」；具体层 real_le 为 Or(lt,eq)   *)
(* 两支，取支需序上的符号判定，非现有基础引理可构造）——故以全称前提显式承载，        *)
(* 如实申报为条件供给而非无条件供给。 *)
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

(* ============ §C · weak_trich 具体实例供给（可分离节） ============ *)
(* 边界注记：弱三分无法从抽象接口字段导出（序比较 Or 形需符号判定）。本节为           *)
(* 具体实例供给：real_weak_trich 为已证引理（Qed 闭合；弱三分在 Real 实例上成立，      *)
(* req 在该实例上即 real_eq）——直接推得，无新增辅件。本节可整体移除而不影响他件。      *)
Theorem uabd1s14_cau_weak_trich_supply :
  forall x y : Real, Not (lt x y) -> Not (lt y x) -> req x y.
Proof.
  intros x y H1 H2.
  exact (real_weak_trich x y H1 H2).
Qed.

(* ============ 假设审计（Print Assumptions 全 Closed 为判据） ============ *)

Print Assumptions uabd1s14_cau_opp_opp.
Print Assumptions uabd1s14_cau_strict_concavity_supply.
Print Assumptions uabd1s14_cau_strong_concavity_supply.
Print Assumptions uabd1s14_cau_entropy_tangent_supply.
Print Assumptions uabd1s14_cau_r_arch_pow_supply.
Print Assumptions uabd1s14_cau_lim_metric_supply.
Print Assumptions uabd1s14_cau_cond_pack2_supplied.
Print Assumptions uabd1s14_cau_weak_trich_supply.
