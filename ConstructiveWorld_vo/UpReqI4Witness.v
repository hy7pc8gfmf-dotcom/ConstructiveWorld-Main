(* ============================================================ *)
(* UpReqI4Witness.v *)
(* *)
(* 目的： 结论 I4 证书位的实例化（无条件形）。 *)
(* 主件： i4b_policy_iter_kl_pow_mono_unconditional：经 t30 见证族去假设位化。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、G07_KLWall、UpReqGeomD、UpGeomB、UpReqGeomIter、UpReqPowMonoBridge、UpReqI4Bridge。 *)
(* 备注： 实例化件：t30_kl_term_eq_zero 等见证把桥件假设位落实为零前提形。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqI4Witness.v —— 结论 I4 证书位实例化席 T30（独占 CoreN 0）          *)
(*   使命＝为具体 geodi 实例补供 Or 形 0 ≤ KL_0 证书，使结论 I4 的        *)
(*   消费位（UpReqI4Bridge 主桥件2 的 Hkl0or 前提）从接口化降为          *)
(*   「证书内部构造」：调用方不再提供 KL_0 形态的任何前提，只需提供      *)

(* ---------------------------------------------------------------- *)
(* 上游链（全只读消费，既有绿件零改）：                                   *)
(*   · T1 端点件 klst_kl_energy_nonconst（G07 Part G，KL>0 无条件主件）： *)
(*     双归一化＋逐项双向弱序＋s0 处任一方向严格分离 ⟹ 0 < Σ kl_term。   *)

(*   · klst_gibbs_core_zero（G07）：r==p ⟹ kl_term＋(p−r) == 0——        *)

(*   · T20 接口件 i4b_kl0_or_of_lt / i4b_kl0_or_of_eq（UpReqI4Bridge     *)

(*   · T20 主桥 i4b_policy_iter_kl_pow_mono_B（件2）：结论 I4 消费位，   *)

(*   · geod_lsum（UpReqGeomD L218）≡ real_list_sum nat f (seq 0 n)——     *)
(*     定义性展开即与 G07 的 list 形（l1 ++ s0 :: l2）无磨合对接。        *)
(* ---------------------------------------------------------------- *)
(* 件清单（11 件全 Qed）：                                               *)
(*   件W0 t30_id_nat_rev：库内 Set 层等同 Id 的运输件（Id 非可改写等号，  *)
(*       仅供 destruct 完成，语句面 Set 值）；                            *)
(*   件W0b t30_seq_split：seq 0 (Nat.succ(j+k)) 的 l1++j::l2 分解——       *)
(*       内部改写通道件（结论为 stdlib 等号，仅作 rewrite 通道用，        *)
(*       非结果语句面；结果面 W2–W8 全 Set 值）；                         *)
(*   件W1a t30_lsum_zero_seq / 件W1b t30_lsum_zero：全零和归零；          *)
(*   件W2 t30_kl_term_eq_zero：逐项归零（klst_gibbs_core_zero 运输）；    *)
(*   件W3 t30_kl0_eq_of_pointwise：inr 支——逐点 r==p ⟹ KL_0 == 0；       *)
(*   件W4 t30_kl0_lt_of_div：inl 支——逐点双向可比＋j 处任一方向严格       *)
(*       分离 ⟹ 0 < KL_0（klst_kl_energy_nonconst 在 geodi 实例化）；     *)
(*   件W5 t30_kl0_or_of_case：组装——分布层情形见证 Or ⟹ Or 形 0≤KL_0    *)
(*       （inl 支经件0a、inr 支经件0b，两支接口件全量复用）；             *)
(*   件W6 i4b_policy_iter_kl_pow_mono_unconditional：无条件闭合主件——    *)
(*       结论 I4 目标形「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」，前提包＝       *)

(*       内部合成（消费 T20 主桥件2 一次直连）；                          *)
(*   件W7/W8 i4bw_..._nonconst / i4bw_..._const：两支端到端实例——        *)
(*       单支见证即全闭合的分布级演示（T20 件3 的分布级升级版）。         *)
(* ---------------------------------------------------------------- *)
(* 诚实边界（残差精确形状，承 T1 结论）：                                 *)
(*   · 逐项可比前提 Or (real_le (r i) (p i)) (real_le (p i) (r i)) 的    *)
(*     去除＝对任意实对供三分判定见证（LLPO 形），非直觉主义可证         *)
(*     （T1 卡消解(a) 终点结论在案）；                                   *)
(*   · 分离见证位的「情形 Or」（逐点相等 支 / 分离见证 支）同理不可      *)
(*     去除——KL_0>0 与 KL_0==0 的构造性可分缺口在上游（实对序判定），   *)
(*     不在 KL_0 证书侧；本件把缺口从「KL_0 形前提」下推到「分布层       *)
(*     数据见证」，已到该链路的直觉主义终点；                            *)
(*   · 具体实例两侧见证皆可构造：r:=均匀分布、p 为任一有理可算扰动       *)
(*     分布时，可比性与分离见证按有理序可判定逐点供给。                  *)
(* 红线自检：零未闭合证明（全件Qed）；零新依赖面（仅 Require 既有绿库）； *)
(*   语句面全 Set 值（real_le/real_lt/real_eq/NatLt/NatLe 全 Set 值，    *)
(*   Or:=A+B 库内 Set 和型；情形见证用 sigT 不用存在命题，零命题泄露；   *)
(*   唯一 stdlib 等号出现在 W0b 内部改写通道，见其登记表行）；              *)
(*   纯 term-mode 组装（real_eq 非可改写等号，全链 real_eq_trans 运输；  *)
(*   库内 Id 亦非可改写等号，全链 destruct 完成件 W0 运输）；             *)
(*   禁词全零（按全文件计含头注，中文语义表述不引字面量）。              *)
(* 编译配方（vo 树前置；EMPTY 处为空串实参，引号从略防注释串警告；       *)
(*   cpu_guard 包装零裸调，CoreN 0；先 -vos 秒审再全量）：                *)

(* ============================================================ *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpGeomB.
Require Import UpReqGeomIter.
Require Import UpReqPowMonoBridge.
Require Import UpReqI4Bridge.

(* ============================================================ *)
(* 〇、桥件：库内 Id 运输＋seq 分解（对接 G07 的 l1 ++ s0 :: l2 形）      *)
(* ============================================================ *)

(* 件W0：Set 层等同运输双向件（Id 非可改写等号，destruct 完成后即定义性换元） *)
Lemma t30_id_nat_fwd : forall (n m : nat) (P : nat -> Set),
  Id n m -> P n -> P m.
Proof.
  intros n m P Hnid H. destruct Hnid. exact H.
Qed.

Lemma t30_id_nat_rev : forall (n m : nat) (P : nat -> Set),
  Id n m -> P m -> P n.
Proof.
  intros n m P Hnid H. destruct Hnid. exact H.
Qed.

(* 件W0b：内部改写通道件（stdlib 等号，仅 rewrite 用） *)
Lemma t30_seq_split : forall j k : nat,
  List.seq 0 (Nat.succ (j + k)) =
  List.seq 0 j ++ (j :: List.seq (Nat.succ j) k)%list.
Proof.
  intros j k.
  replace (Nat.succ (j + k)) with (j + Nat.succ k).
  - rewrite List.seq_app. apply eq_refl.
  - apply Nat.add_succ_r.
Qed.

(* 件W1a：全零函数的 list 和归零（起点概括，归纳完成） *)
Lemma t30_lsum_zero_seq : forall len s : nat,
  real_eq (real_list_sum nat (fun _ : nat => real_zero) (List.seq s len))
          real_zero.
Proof.
  induction len as [| len IH]; intros s.
  - apply real_eq_refl.
  - change (real_eq
              (real_plus real_zero
                 (real_list_sum nat (fun _ : nat => real_zero)
                    (List.seq (Nat.succ s) len)))
              real_zero).
    apply (RealSetoid.real_eq_plus_compat real_zero
             (real_list_sum nat (fun _ : nat => real_zero)
                (List.seq (Nat.succ s) len))
             real_zero real_zero).
    + apply real_eq_refl.
    + apply IH.
Qed.

(* 件W1b：geod_lsum 形全零和归零 *)
Lemma t30_lsum_zero : forall n : nat,
  real_eq (geod_lsum n (fun _ : nat => real_zero)) real_zero.
Proof.
  intros n. unfold geod_lsum. apply t30_lsum_zero_seq.
Qed.

(* ============================================================ *)
(* 一、inr 支：逐点 r==p ⟹ KL_0 == 0                                     *)
(* ============================================================ *)

(* 件W2：逐项归零——klst_gibbs_core_zero（kl_term＋(p−r)==0）经          *)
(*   real_plus_zero / 加法换形运输到 kl_term == 0                        *)
Lemma t30_kl_term_eq_zero : forall (u v : Real)
    (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
  real_eq u v -> real_eq (real_kl_term u v Hu Hv) real_zero.
Proof.
  intros u v Hu Hv Huv.
  assert (Heq0 : real_eq real_zero (real_plus v (real_opp u))).
  { apply (real_eq_trans _ (real_plus v (real_opp v)) _).
    - apply real_eq_sym. exact (real_plus_opp v).
    - exact (RealSetoid.real_eq_plus_compat v (real_opp v) v (real_opp u)
               (real_eq_refl v)
               (real_eq_sym (real_opp u) (real_opp v)
                  (RealSetoid.real_eq_opp_compat u v Huv))). }
  apply (real_eq_trans _ (real_plus (real_kl_term u v Hu Hv) real_zero) _).
  - exact (real_eq_sym _ _ (real_plus_zero (real_kl_term u v Hu Hv))).
  - apply (real_eq_trans
             _ (real_plus (real_kl_term u v Hu Hv)
                  (real_plus v (real_opp u))) _).
    + exact (RealSetoid.real_eq_plus_compat (real_kl_term u v Hu Hv)
               real_zero (real_kl_term u v Hu Hv)
               (real_plus v (real_opp u))
               (real_eq_refl (real_kl_term u v Hu Hv)) Heq0).
    + exact (klst_gibbs_core_zero u v Hu Hv Huv).
Qed.

(* 件W3：inr 支主件——逐点相等 ⟹ KL_0 == 0（逐项 ext＋件W1b） *)
Lemma t30_kl0_eq_of_pointwise : forall (n : nat) (r p : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i)),
  (forall i : nat, real_eq (r i) (p i)) ->
  real_eq (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))) real_zero.
Proof.
  intros n r p Hr Hp Hpt.
  apply (real_eq_trans _ (geod_lsum n (fun _ : nat => real_zero)) _).
  - unfold geod_lsum.
    exact (real_list_sum_ext nat
             (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
             (fun _ : nat => real_zero) (List.seq 0 n)
             (fun i : nat =>
                t30_kl_term_eq_zero (r i) (p i) (Hr i) (Hp i) (Hpt i))).
  - exact (t30_lsum_zero n).
Qed.

(* ============================================================ *)
(* 二、inl 支：逐点双向可比＋一处严格分离 ⟹ 0 < KL_0                     *)
(*   ＝ klst_kl_energy_nonconst（G07 KL>0 无条件主件）在 geodi 实例化    *)
(* ============================================================ *)

(* 件W4：inl 支主件。j,k 为分离站位的 seq 分解数据（Set 值 Id 见证）。 *)
Lemma t30_kl0_lt_of_div : forall (n : nat) (r p : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hpq : forall i : nat, Or (real_le (r i) (p i)) (real_le (p i) (r i)))
    (j k : nat) (Hn : Id n (Nat.succ (j + k)))
    (Hdiv : Or (real_lt (r j) (p j)) (real_lt (p j) (r j))),
  real_lt real_zero (geod_lsum n (fun i : nat =>
                      real_kl_term (r i) (p i) (Hr i) (Hp i))).
Proof.
  intros n r p Hr Hp Hnormr Hnormp Hpq j k Hn Hdiv.
  assert (Hnormr' : real_eq
             (real_list_sum nat r (List.seq 0 (Nat.succ (j + k)))) real_one).
  { apply (t30_id_nat_fwd n (Nat.succ (j + k))
             (fun m : nat =>
                real_eq (real_list_sum nat r (List.seq 0 m)) real_one)).
    - exact Hn.
    - unfold geod_lsum in Hnormr. exact Hnormr. }
  rewrite (t30_seq_split j k) in Hnormr'.
  assert (Hnormp' : real_eq
             (real_list_sum nat p (List.seq 0 (Nat.succ (j + k)))) real_one).
  { apply (t30_id_nat_fwd n (Nat.succ (j + k))
             (fun m : nat =>
                real_eq (real_list_sum nat p (List.seq 0 m)) real_one)).
    - exact Hn.
    - unfold geod_lsum in Hnormp. exact Hnormp. }
  rewrite (t30_seq_split j k) in Hnormp'.
  apply (t30_id_nat_rev n (Nat.succ (j + k))
           (fun m : nat =>
              real_lt real_zero (geod_lsum m (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))).
  - exact Hn.
  - unfold geod_lsum. rewrite (t30_seq_split j k).
    exact (klst_kl_energy_nonconst nat (List.seq 0 j) j
             (List.seq (Nat.succ j) k) r p Hr Hp Hpq
             Hnormr' Hnormp' Hdiv).
Qed.

(* ============================================================ *)
(* 三、组装：分布层情形见证 Or ⟹ Or 形 0 ≤ KL_0                          *)
(* ============================================================ *)

(* 分离见证形（全 Set 值：sigT 三层，站位 j＋seq 分解 k＋任一方向严格分离） *)
Definition t30_div_witness (n : nat) (r p : nat -> Real) : Set :=
  sigT (fun j : nat =>
    sigT (fun k : nat =>
      sigT (fun _ : Id n (Nat.succ (j + k)) =>
        Or (real_lt (r j) (p j)) (real_lt (p j) (r j))))).

(* 件W5：组装件。左支（逐点相等）走 T20 件0b；右支（分离见证）走 T20 件0a。 *)
Lemma t30_kl0_or_of_case : forall (n : nat) (r p : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hpq : forall i : nat, Or (real_le (r i) (p i)) (real_le (p i) (r i)))
    (Hcase : Or (forall i : nat, real_eq (r i) (p i))
                (t30_div_witness n r p)),
  real_le real_zero (geod_lsum n (fun i : nat =>
                      real_kl_term (r i) (p i) (Hr i) (Hp i))).
Proof.
  intros n r p Hr Hp Hnormr Hnormp Hpq Hcase.
  destruct Hcase as [Hpt | Hw].
  - exact (i4b_kl0_or_of_eq
             (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i)))
             (t30_kl0_eq_of_pointwise n r p Hr Hp Hpt)).
  - destruct Hw as [j [k [Hn Hdiv]]].
    exact (i4b_kl0_or_of_lt
             (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i)))
             (t30_kl0_lt_of_div n r p Hr Hp Hnormr Hnormp Hpq j k Hn Hdiv)).
Qed.

(* ============================================================ *)

(*   语句与 UpReqI4Bridge 件2 逐字同形，唯一变动＝Hkl0or 前提位换成      *)
(*   「逐点双向可比＋分布层情形见证」两个数据级前提。                    *)
(* ============================================================ *)

Lemma i4b_policy_iter_kl_pow_mono_unconditional :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Hpq : forall i : nat, Or (real_le (r i) (p i)) (real_le (p i) (r i)))
    (Hcase : Or (forall i : nat, real_eq (r i) (p i))
                (t30_div_witness n r p))
    (t t1 : nat) (Hle : NatLe t t1),
  real_le_b
    (geod_lsum n (fun i : nat =>
        real_kl_term (r i)
          (geodi_iterate n r Hr eta p Hp Hn t1 i)
          (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Hpq Hcase t t1 Hle.
  exact (i4b_policy_iter_kl_pow_mono_B n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn
           (t30_kl0_or_of_case n r p Hr Hp Hnormr Hnormp Hpq Hcase)
           t t1 Hle).
Qed.

(* ============================================================ *)
(* 五、两支端到端实例：单支见证即全闭合（分布级演示）                     *)
(* ============================================================ *)

(* 件W7：nonconst 支端到端——逐点双向可比＋j 处严格分离 ⟹ 结论 I4 目标形 *)
Lemma i4bw_policy_iter_kl_pow_mono_nonconst :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Hpq : forall i : nat, Or (real_le (r i) (p i)) (real_le (p i) (r i)))
    (j k : nat) (Hn' : Id n (Nat.succ (j + k)))
    (Hdiv : Or (real_lt (r j) (p j)) (real_lt (p j) (r j)))
    (t t1 : nat) (Hle : NatLe t t1),
  real_le_b
    (geod_lsum n (fun i : nat =>
        real_kl_term (r i)
          (geodi_iterate n r Hr eta p Hp Hn t1 i)
          (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Hpq j k Hn' Hdiv t t1 Hle.
  exact (i4b_policy_iter_kl_pow_mono_B n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn
           (i4b_kl0_or_of_lt
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i)))
              (t30_kl0_lt_of_div n r p Hr Hp Hnormr Hnormp Hpq j k Hn' Hdiv))
           t t1 Hle).
Qed.

(* 件W8：const 支端到端——逐点相等 ⟹ 结论 I4 目标形（T20 件3 的分布级升级） *)
Lemma i4bw_policy_iter_kl_pow_mono_const :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Hpt : forall i : nat, real_eq (r i) (p i))
    (t t1 : nat) (Hle : NatLe t t1),
  real_le_b
    (geod_lsum n (fun i : nat =>
        real_kl_term (r i)
          (geodi_iterate n r Hr eta p Hp Hn t1 i)
          (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Hpt t t1 Hle.
  exact (i4b_policy_iter_kl_pow_mono_B n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn
           (i4b_kl0_or_of_eq
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i)))
              (t30_kl0_eq_of_pointwise n r p Hr Hp Hpt))
           t t1 Hle).
Qed.

(* ============================================================ *)
(* 六、假设审计（全件 Closed，证据在编译日志）                            *)
(* ============================================================ *)

Print Assumptions t30_id_nat_fwd.
Print Assumptions t30_id_nat_rev.
Print Assumptions t30_seq_split.
Print Assumptions t30_lsum_zero_seq.
Print Assumptions t30_lsum_zero.
Print Assumptions t30_kl_term_eq_zero.
Print Assumptions t30_kl0_eq_of_pointwise.
Print Assumptions t30_kl0_lt_of_div.
Print Assumptions t30_kl0_or_of_case.
Print Assumptions i4b_policy_iter_kl_pow_mono_unconditional.
Print Assumptions i4bw_policy_iter_kl_pow_mono_nonconst.
Print Assumptions i4bw_policy_iter_kl_pow_mono_const.

(* ============================================================ *)
(* 尾注：诚实登记表                                                        *)
(* 【对接判定】结论 I4 消费位（UpReqGeomIter 尾注）所指缺口，经 T20      *)

(*   消费位需求满足且调用方不再持有 KL_0 形前提；主件结论与件2 逐字      *)
(*   同形，结论 I4 目标形「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」无条件于      *)
(*   KL_0 证书成立。                                                    *)
(* 【残差精确形状】情形 Or 前提（逐点相等 支 / 分离见证 支）与逐点双向   *)
(*   可比前提的去除等价于实对序的三分判定见证（LLPO 形），非直觉主义    *)
(*   可证（T1 卡消解终点结论同源）；该缺口属上游数据层，非 KL_0 证书     *)

(*   可判定逐点供给（如均匀参考分布对有理可算扰动分布）。                *)

(*   G3 提取探针 Obj.magic=0（_t30_g3.v，产物验后即删）。                *)
(* ============================================================ *)
