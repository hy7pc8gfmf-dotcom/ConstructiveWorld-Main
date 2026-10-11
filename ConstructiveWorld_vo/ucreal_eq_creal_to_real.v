(* ================================================================== *)
(* ucreal_eq_creal_to_real.v —— 使命：本件形式化标准库 CReal 相等     *)
(*       到库实数相等的转移，即 CRealEq (ucreal_of_real X)             *)
(*       (ucreal_of_real Y) -> real_eq X Y。                           *)
(*                                                                    *)
(* 依赖：标准库 QArith、Qpower、Qabs、ZArith、Lia、Lqa、QExtra、      *)
(*       ConstructiveCauchyReals；库内 ucreal_bridge、S01_BaseRing、   *)
(*       S02_CauchyComplete。                                         *)
(* 对标：Stdlib.Reals.Cauchy.ConstructiveCauchyReals（CRealEq_diff）。 *)
(* 构造性注记：语句面 Set/Type 承载——辅助件结论以 sigT 与 QltT 承载，  *)
(*       主定理结论 real_eq 系 Set 层 sigT 尾差形；深度见证由标准库    *)
(*       阿基米德引理 QarchimedeanLowExp2_Z 供给，尾项界由 cauchy 的   *)
(*       sigT 见证供给；Prop 否定形前提 CRealEq 仅经 CRealEq_diff     *)
(*       正向使用为逐点量化界（证明体内构造性 Prop 推导），全程零公理、 *)
(*       零承认、零经典逻辑、不引入排中律。                           *)
(* 编译配方：coqc -native-compiler no -q -Q world ""                  *)
(*       world\ucreal_eq_creal_to_real.v（cpu_guard 包裹）。          *)
(* ================================================================== *)

From Stdlib Require Import QArith.
From Stdlib Require Import Qpower.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import QExtra.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import ucreal_bridge.

(* ================= §1 负指数二之幂的深度见证 ================= *)

(** 深度见证：对任意正有理数 [e]，存在自然数 [K] 使 [2 ^ (- K)] 小于
    [e]，结论以 sigT 与 QltT 承载。证明策略：由标准库阿基米德引理
    [QarchimedeanLowExp2_Z] 取指数 [z]，深度取
    [Z.to_nat (Z.max (- z) 0)]，再由幂函数单调性 [ucreal_pow2_le_mono]
    对齐两侧指数。 *)

Lemma ucreal_eq_depth_down :
  forall e : Q, QltT 0 e ->
    sigT (fun K : nat => QltT (2 ^ Z.opp (Z.of_nat K)) e).
Proof.
  intros e Hpos.
  destruct (QarchimedeanLowExp2_Z e (QltT_to_Qlt _ _ Hpos)) as [z Hz].
  exists (Z.to_nat (Z.max (Z.opp z) 0)).
  assert (Hznat : Z.of_nat (Z.to_nat (Z.max (Z.opp z) 0)) = Z.max (Z.opp z) 0)
    by (apply Z2Nat.id; lia).
  assert (Hle : (Z.opp (Z.of_nat (Z.to_nat (Z.max (Z.opp z) 0))) <= z)%Z)
    by (rewrite Hznat; lia).
  pose proof (ucreal_pow2_le_mono _ _ Hle) as Hmono.
  apply Qlt_to_QltT. lra.
Qed.

(* ================= §2 尾差界与等式转移主定理 ================= *)

(** 逐 eps 尾差见证：设转换 [ucreal_of_real] 下 [X] 与 [Y] 的像满足
    [CRealEq]，则对任意正有理数 [eps] 存在尾界指标 [N]，使 [N] 之后
    同指标尾差绝对值小于 [eps]，结论以 sigT 与 QltT 承载。证明策略：
    取公共深度 [K] 为柯西模量与深度见证阈值的最大值，转换在指标
    [- K] 处的取样位置 [mx = ucreal_mod ux cx K] 与
    [my = ucreal_mod uy cy K] 兼作柯西公共深点；对任意
    [n >= max mx my]，三角不等式给出尾差
    [< eps/4 + 2 * 2 ^ (- K) + eps/4 < eps]；其中 [- K] 处的逐点绝对
    值界由 [CRealEq_diff] 的正向在证明体内直接实例化。 *)

Lemma ucreal_eq_tail_eps :
  forall X Y : Real,
    CRealEq (ucreal_of_real X) (ucreal_of_real Y) ->
    forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
        QltT (Qabs (projT1 X n - projT1 Y n)) eps).
Proof.
  intros X Y Hceq eps Hpos.
  destruct X as [ux cx]. destruct Y as [uy cy].
  apply QltT_to_Qlt in Hpos.
  assert (Hpos4 : QltT 0 (eps * (1 # 4))%Q) by (apply Qlt_to_QltT; lra).
  destruct (cx (eps * (1 # 4))%Q Hpos4) as [Nu HNu].
  destruct (cy (eps * (1 # 4))%Q Hpos4) as [Nv HNv].
  destruct (ucreal_eq_depth_down (eps * (1 # 4))%Q Hpos4) as [K0 HK0].
  apply QltT_to_Qlt in HK0.
  remember (Nat.max K0 (Nat.max Nu Nv)) as K eqn:HKdef.
  assert (HK0le : (K0 <= K)%nat) by lia.
  assert (HNuK : (Nu <= K)%nat) by lia.
  assert (HNvK : (Nv <= K)%nat) by lia.
  pose proof ((proj1 (CRealEq_diff
              (ucreal_of_real (existT (fun u : Qseq => cauchy u) ux cx))
              (ucreal_of_real (existT (fun u : Qseq => cauchy u) uy cy))))
             Hceq (Z.opp (Z.of_nat K))) as Hmg.
  assert (Hsx : seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) ux cx))
                    (Z.opp (Z.of_nat K))
                = ux (ucreal_mod ux cx (Z.to_nat (Z.abs (Z.opp (Z.of_nat K))))))
    by reflexivity.
  assert (Hsy : seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) uy cy))
                    (Z.opp (Z.of_nat K))
                = uy (ucreal_mod uy cy (Z.to_nat (Z.abs (Z.opp (Z.of_nat K))))))
    by reflexivity.
  rewrite Hsx, Hsy in Hmg.
  assert (Hidx : Z.to_nat (Z.abs (Z.opp (Z.of_nat K))) = K).
  { assert (H0 : (0 <= Z.of_nat K)%Z) by lia.
    rewrite Z.abs_opp. rewrite (Z.abs_eq (Z.of_nat K) H0).
    apply Nat2Z.id. }
  rewrite Hidx in Hmg.
  assert (HZle : (Z.opp (Z.of_nat K) <= Z.opp (Z.of_nat K0))%Z) by lia.
  pose proof (ucreal_pow2_le_mono _ _ HZle) as Hmono.
  apply Qabs_Qle_condition in Hmg. destruct Hmg as [Hmg1 Hmg2].
  assert (Hmxge : (K <= ucreal_mod ux cx K)%nat)
    by (unfold ucreal_mod; apply Nat.le_max_r).
  assert (Hmyge : (K <= ucreal_mod uy cy K)%nat)
    by (unfold ucreal_mod; apply Nat.le_max_r).
  remember (ucreal_mod ux cx K) as mx eqn:Hmxdef.
  remember (ucreal_mod uy cy K) as my eqn:Hmydef.
  exists (Nat.max mx my).
  intros n Hn.
  cbn [projT1].
  assert (Hnle : (Nat.max mx my <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hnmx : (mx <= n)%nat) by lia.
  assert (Hnmy : (my <= n)%nat) by lia.
  assert (Hnumx : (Nu <= mx)%nat) by lia.
  assert (Hnumn : (Nu <= n)%nat) by lia.
  assert (Hnymy : (Nv <= my)%nat) by lia.
  assert (Hnynn : (Nv <= n)%nat) by lia.
  pose proof (HNu n mx (NatLe_lift _ _ Hnumn) (NatLe_lift _ _ Hnumx)) as Hs1.
  pose proof (HNv n my (NatLe_lift _ _ Hnynn) (NatLe_lift _ _ Hnymy)) as Hs2.
  apply QltT_to_Qlt in Hs1. apply Qabs_Qlt_condition in Hs1.
  destruct Hs1 as [Hs1 Hs1'].
  apply QltT_to_Qlt in Hs2. apply Qabs_Qlt_condition in Hs2.
  destruct Hs2 as [Hs2 Hs2'].
  apply Qlt_to_QltT.
  apply (proj2 (Qabs_Qlt_condition (ux n - uy n) eps)).
  split; lra.
Qed.

(** 主定理：标准库 [CReal] 相等 [CRealEq] 经转换映射 [ucreal_of_real]
    转移为库实数相等 [real_eq]，由逐 eps 尾差见证
    [ucreal_eq_tail_eps] 按定义组装。 *)

Theorem ucreal_eq_creal_to_real :
  forall X Y : Real,
    CRealEq (ucreal_of_real X) (ucreal_of_real Y) -> real_eq X Y.
Proof.
  intros X Y Hceq eps Hpos.
  exact (ucreal_eq_tail_eps X Y Hceq eps Hpos).
Qed.

(* ================= §3 审计与提取语句 ================= *)

Print Assumptions ucreal_eq_depth_down.
Print Assumptions ucreal_eq_tail_eps.
Print Assumptions ucreal_eq_creal_to_real.

From Stdlib Require Import Extraction.
Extraction "ucreal_eq_creal_to_real_extract.ml" ucreal_eq_creal_to_real.
