(* ==========================================================================)
   UpReqI4Witness.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：i4b_kl0_or_of_lt、i4b_kl0_or_of_eq、i4b_pow_kl_mono_le_b、i4b_policy_iter_kl_pow_mono_B、i4b_policy_iter_kl_pow_mono_eq0、t30_id_nat_fwd、t30_id_nat_rev、t30_seq_split、t30_lsum_zero_seq。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpGeomB.
Require Import UpReqGeomIter.
Require Import UpReqPowMonoBridge.

(* ================= §1 i4b_kl0_or_of_lt 族 ================= *)
(* 〇、证书位接口：Or 形 0 ≤ KL_0 的两支可通行构造                        *)

(* 件0a：严格见证支。0 < KL_0 直接给 Or 左支（real_le = lt ∨ eq）。 *)
Lemma i4b_kl0_or_of_lt : forall KL0 : Real,
  real_lt real_zero KL0 -> real_le real_zero KL0.
Proof.
  intros KL0 H. exact (inl H).
Qed.

(* 件0b：等式反射支。KL_0 == 0 经 real_eq_sym 运输＋Or 右支自反。 *)
Lemma i4b_kl0_or_of_eq : forall KL0 : Real,
  real_eq KL0 real_zero -> real_le real_zero KL0.
Proof.
  intros KL0 Heq.
  exact (RealSetoid.real_le_id_l real_zero KL0 KL0
           (real_eq_sym KL0 real_zero Heq) (real_le_refl KL0)).
Qed.

(* 一、结论 I4 缺口形状实例闭合：κ^{t1}·KL_0 ≤_B κ^t·KL_0                 *)
(*   ＝ UpReqGeomIter 尾注所指「κ^{t1}·KL_0 ≤ κ^t·KL_0+δ 的 le_b 乘法    *)
(*   保序闭包（非负右因子版）」在使用点的单点落成（④件1 ∘ ③powb 单调）。 *)

Lemma i4b_pow_kl_mono_le_b : forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (t t1 : nat) (Hle : NatLe t t1),
  real_le real_zero
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i) (p i) (Hr i) (Hp i))) ->
  real_le_b
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t1)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i))))
    (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
               (geod_lsum n (fun i : nat =>
                  real_kl_term (r i) (p i) (Hr i) (Hp i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp t t1 Hle Hkl0or.
  exact (x3d_le_b_mult_r_nonneg_or
           (powb_pow (real_plus real_one (real_opp eta)) t1)
           (powb_pow (real_plus real_one (real_opp eta)) t)
           (geod_lsum n (fun i : nat =>
              real_kl_term (r i) (p i) (Hr i) (Hp i)))
           (powb_one_minus_eta_mono_dec eta t t1 Heta Hlt1 Hle)
           Hkl0or).
Qed.

(* 二、主桥：结论 I4 使用位对接件（X3d 草案 x3d_i4_bridge_draft 正式化）  *)

Lemma i4b_policy_iter_kl_pow_mono_B :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Hkl0or : real_le real_zero
                (geod_lsum n (fun i : nat =>
                   real_kl_term (r i) (p i) (Hr i) (Hp i))))
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
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Hkl0or t t1 Hle.
  apply (real_le_b_trans
           (geod_lsum n (fun i : nat =>
              real_kl_term (r i)
                (geodi_iterate n r Hr eta p Hp Hn t1 i)
                (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t1 i)))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t1)
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))
           (real_mult (powb_pow (real_plus real_one (real_opp eta)) t)
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))).
  (* 跳①：主件 B 伴件（t1 站位，UpReqGeomIter 主定理伴件） *)
  - exact (geodi_policy_iter_kl_geom_iter_B n r Hr eta Heta Hlt1 p Hp
             Hnormr Hnormp Hn t1).
  (* 跳②：件1（④∘③，非负右因子取 KL_0） *)
  - exact (i4b_pow_kl_mono_le_b n r Hr eta Heta Hlt1 p Hp t t1 Hle Hkl0or).
Qed.

(* 三、证书支路实例：eq 支端到端闭合（证书位接口使用演示）                *)

Lemma i4b_policy_iter_kl_pow_mono_eq0 :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (Heq0 : real_eq (geod_lsum n (fun i : nat =>
                       real_kl_term (r i) (p i) (Hr i) (Hp i))) real_zero)
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
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn Heq0 t t1 Hle.
  exact (i4b_policy_iter_kl_pow_mono_B n r Hr eta Heta Hlt1 p Hp
           Hnormr Hnormp Hn
           (i4b_kl0_or_of_eq (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i))) Heq0)
           t t1 Hle).
Qed.

(* 四、假设审计（全件 Closed，证据在编译日志）                            *)

Print Assumptions i4b_kl0_or_of_lt.
Print Assumptions i4b_kl0_or_of_eq.
Print Assumptions i4b_pow_kl_mono_le_b.
Print Assumptions i4b_policy_iter_kl_pow_mono_B.
Print Assumptions i4b_policy_iter_kl_pow_mono_eq0.

(* 尾注：诚实登记表                                                        *)
(*   乘法保序闭包（非负右因子版）」已由 UpReqPowMonoBridge 件1 落库；     *)

(*   结论 I4 目标形「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」在补充 Or 形证书     *)
(*   Hkl0or 下全闭合——使用位需求满足（草案残差即本证书位）。             *)
(*   · 库内已有全为 B 形（geodi_kl_nonneg_B / real_gibbs_inequality_B /  *)
(*     gibbsd_gibbs_inequality），其链根 real_gibbs_core_eps 与          *)

(*     逐 eps 完成不给 Or 分支判定（KL_0>0 与 KL_0==0 构造性不可分，     *)
(*     gibbs 等号条件 r==p 逐点判定同样不可分），B⟹Or 方向显式假设成立，     *)

(*   · 两支可通行支路已登记为接口件（件0a lt 支／件0b eq 支）：使用位    *)
(*     上游能供严格见证或等式见证时任取一支即全闭合（件3 为 eq 支        *)
(*     端到端实例）；                                                    *)
(*   · 有界面 ④件5 亦要求 Or 形 0≤c 前提，同样绕不开本单点——换合成器    *)
(*     变体不消除残差；唯有上游见证，或「sup KL 上界材料＋纯 B 形因子    *)
(*     新合成器」路线（库内上界件显式假设，见 UpReqGeomIter 尾注）。          *)

(*   G3 提取检验 Obj.magic=0（，产物目录验后即删）。            *)
(* ================= §2 t30_id_nat_fwd 族 ================= *)
(* 〇、桥接引理：库内 Id 运输＋seq 分解（对接 G07 的 l1 ++ s0 :: l2 形）      *)

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

(* 一、inr 支：逐点 r==p ⟹ KL_0 == 0                                     *)

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

(* 二、inl 支：逐点双向可比＋一处严格分离 ⟹ 0 < KL_0                     *)
(*   ＝ klst_kl_energy_nonconst（G07 KL>0 无条件主件）在 geodi 实例化    *)

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

(* 三、组装：分布层情形见证 Or ⟹ Or 形 0 ≤ KL_0                          *)

(* 分离见证形（全 Set 值：sigT 三层，站位 j＋seq 分解 k＋任一方向严格分离） *)
Definition t30_div_witness (n : nat) (r p : nat -> Real) : Set :=
  sigT (fun j : nat =>
    sigT (fun k : nat =>
      sigT (fun _ : Id n (Nat.succ (j + k)) =>
        Or (real_lt (r j) (p j)) (real_lt (p j) (r j))))).

(* 件W5：组装件。左支（逐点相等）走  件0b；右支（分离见证）走  件0a。 *)
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


(*   语句与 UpReqI4Bridge 件2 逐字同形，唯一变动＝Hkl0or 前提位换成      *)
(*   「逐点双向可比＋分布层情形见证」两个数据级前提。                    *)

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

(* 五、两支端到端实例：单支见证即全闭合（分布级演示）                     *)

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

(* 件W8：const 支端到端——逐点相等 ⟹ 结论 I4 目标形（ 件3 的分布级升级） *)
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

(* 六、假设审计（全件 Closed，证据在编译日志）                            *)

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

(* 尾注：诚实登记表                                                        *)

(*   使用位需求满足且调用方不再持有 KL_0 形前提；主件结论与件2 逐字      *)
(*   同形，结论 I4 目标形「t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0」无条件于      *)
(*   KL_0 证书成立。                                                    *)
(*   可比前提的去除等价于实对序的三分判定见证（LLPO 形），非直觉主义    *)
(*   可证（T1 卡消解终点结论同源）；该缺口属上游数据层，非 KL_0 证书     *)

(*   可判定逐点供给（如均匀参考分布对有理可算扰动分布）。                *)

(*   G3 提取检验 Obj.magic=0（产物验后即删）。                *)
