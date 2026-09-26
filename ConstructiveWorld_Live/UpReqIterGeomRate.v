(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   igr_geom_step_discharged_B（原 L286，4 句玩具证）                    *)
(*   igr_le_plus_r（原 L202，2 句玩具证）                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqIterGeomRate.v                                          *)
(*                                                              *)
(*   在锚内把「单步无假设收缩」与「迭代归纳」闭合：S15 原生实例化消解件      *)
(*   real_step_kl_eta_bound_eps（S15_TailFEPUp.v:1014，Require 首次     *)
(*   被迭代轨道依存）× geodi sigT 迭代骨架（UpReqGeomIter.v）⟹          *)
(*   Real 层真几何率 (1-eta)^t 的锐利几何和误差账与 t·eps 简化账，       *)
(*   Bishop 形 real_le_b 交付——下游零接口假设（S05:4404 Variable       *)
(*   step_kl_eta_bound 的假设位在 Real 层全部由轨道自供给替代：          *)
(*   HZ-参数位 := geodi_zpos（NatLt 非平凡前提），Hqv-参数位 := geodi_next_pos。） *)
(*                                                              *)
(* 交付清单：                                                    *)
(*   W5  igr_geom_step_eps / igr_geom_step_discharged_B           *)
(*       （单步真几何收缩 KL(pi*||pi_{t+1}) <= (1-eta)·KL(pi*||pi_t)+eps  *)
(*        及其 Bishop 形；HZ/Hqv 假设位轨道自足，零接口假设）；          *)
(*   W6  igr_iter_geom_rate_tight_eps / igr_iter_geom_rate_tight   *)
(*       （锐利几何和账 KL_t <= (1-eta)^t·KL_0 + G_t·eps，             *)
(*        G_t = sum_{i<t}(1-eta)^i，real_le 形 + B 形）；               *)
(*       igr_iter_geom_rate_eps / igr_iter_geom_rate                   *)
(*       （t·eps 简化账，real_le 形 + B 形）。                          *)
(*   W7（R3）igr_iter_geom_rate_witness / _one（sigT 四层见证器：         *)
(*       Defined 项级 match t 分派，产出收缩界 Bishop 见证；              *)
(*       S 支拆分路线 igr_ring_scale_inv + igr_iter_budget_witness_S）；  *)
(*       igr_k_select（Q 证书面最小 t 的 Nat 枚举 Defined，C10 同构）。   *)
(*                                                              *)
(* 数学核（锐利核算免几何和恒等式）：                                *)
(*   误差账递归取 G_{S m} := 1 + kappa·G_m（新步误差全额入账、         *)
(*   旧误差 kappa 折扣），则归纳步循环依赖清单                                  *)
(*     kappa·(kappa^m·KL_0 + G_m·eps) + eps                            *)
(*       == kappa^{S m}·KL_0 + (1 + kappa·G_m)·eps                      *)
(*   拆为三个纯 Real 原子环件（igr_ring_step_a/b、igr_ring_reassoc，    *)
(*   destruct+ring 直闭）经 plus-compat 链组合（igr_ring_step），       *)
(*   单步喂定取全额 eps（实例化消解件 eps-参数位任意），eta 严格正前提仅用于      *)
(*   kappa = 1-eta 的正性/le_one 证书与 B 完成器的 D 正性。             *)
(*                                                              *)
(* 移植与核验：                                                  *)
(*   - 迭代骨架/喂定模式移植自 UpReqGeomIter.v:398-419（对子消解        *)
(*     + q 形直供 + 同字面项烘焙）；B 完成器路线对齐                    *)
(*     UpReqGeomIter.v:786-815（real_le_closure 族收尾）。              *)
(*   - 环件 destruct+ring 风格移植自 UpStepKLM3.v（m3_ring_eta_kappa    *)
(*     等模式）；一步收缩的换向依存形对齐 UpStepKLM3.v:432-461。        *)
(*   - 与 UpStepKLM3（M3 迭代副本，同在注册面）的差异：本件以 geodi     *)
(*     轨道为载体（NatLt Set 层非平凡前提）、误差账改锐利几何和形、     *)
(*     交付面为 Bishop 形 real_le_b。                                   *)
(*                                                              *)
(* 公理面：零新增假设位；全件 Qed 闭合；语句面全 Set/Type 值            *)
(* （real_le/real_lt/real_eq/real_le_b/NatLt/sigT），假设申报位      *)
(* 无排序命题承载。                                                     *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith.
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
Require Import G07_KLWall.
Require Import UpReqGeomD.
Require Import UpReqGeomIter.
Import RealInterfaceEnhancedMod.
Local Open Scope nat_scope.

(* ========== 载体定义 ========== *)

(* 几何率底 kappa := 1 - eta *)
Definition igr_kappa (eta : Real) : Real := real_plus real_one (real_opp eta).

(* 锐利误差账：G_t = sum_{i<t} kappa^i，递归 G_O = 0、G_{S m} = 1 + kappa·G_m
   （与逐项和 1 + k + ... + k^{t-1} 等值，核算顺序不同）。 *)
Fixpoint igr_gsum (k : Real) (t : nat) : Real :=
  match t with
  | Datatypes.O => real_zero
  | Datatypes.S m => real_plus real_one (real_mult k (igr_gsum k m))
  end.

(* t·x（nat 重复加；简化账的 t 步误差累积） *)
Fixpoint igr_nmul (t : nat) (x : Real) : Real :=
  match t with
  | Datatypes.O => real_zero
  | Datatypes.S m => real_plus x (igr_nmul m x)
  end.

(* ========== 环 / 序辅助（destruct+ring 风格，移植自 UpStepKLM3） ========== *)

(* 0·x == 0 *)
Lemma igr_mult_zero_r : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof. intros x. destruct x as [v Hv]. apply real_eq_of_zero_diff.
  intro n. simpl. ring. Qed.

(* 左分配：a·(b+c) == a·b + a·c *)
Lemma igr_distrib_l : forall a b c : Real,
  real_eq (real_mult a (real_plus b c)) (real_plus (real_mult a b) (real_mult a c)).
Proof. intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* 右分配：(a+b)·c == a·c + b·c *)
Lemma igr_distrib_r : forall a b c : Real,
  real_eq (real_mult (real_plus a b) c) (real_plus (real_mult a c) (real_mult b c)).
Proof. intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* 重结合：a·(b·c) == (a·b)·c *)
Lemma igr_ring_reassoc : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult (real_mult a b) c).
Proof. intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* 纯原子环件 A：k·(X+Y) + e == k·X + (k·Y + e) *)
Lemma igr_ring_step_a : forall k X Y e : Real,
  real_eq (real_plus (real_mult k (real_plus X Y)) e)
          (real_plus (real_mult k X) (real_plus (real_mult k Y) e)).
Proof. intros k X Y e.
  destruct k as [a Ha]. destruct X as [b Hb]. destruct Y as [c Hc]. destruct e as [f Hf].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* 纯原子环件 B：(1 + k·G)·e == e + k·(G·e) *)
Lemma igr_ring_step_b : forall k G e : Real,
  real_eq (real_mult (real_plus real_one (real_mult k G)) e)
          (real_plus e (real_mult k (real_mult G e))).
Proof. intros k G e.
  destruct k as [a Ha]. destruct G as [b Hb]. destruct e as [f Hf].
  apply real_eq_of_zero_diff. intro n. simpl. ring. Qed.

(* 锐利归纳步总循环依赖清单（组合件；powb_pow/igr_gsum 作原子透传）：
   kappa·(kappa^m·KL0 + G_m·eps) + eps
     == (kappa·kappa^m)·KL0 + (1 + kappa·G_m)·eps。 *)
Lemma igr_ring_step : forall (k KL0 G e : Real) (m : nat),
  real_eq
    (real_plus (real_mult k (real_plus (real_mult (powb_pow k m) KL0)
                                        (real_mult G e)))
               e)
    (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
               (real_mult (real_plus real_one (real_mult k G)) e)).
Proof.
  intros k KL0 G e m.
  pose proof (igr_ring_step_a k (real_mult (powb_pow k m) KL0)
                (real_mult G e) e) as H1.
  pose proof (igr_ring_reassoc k (powb_pow k m) KL0) as H2.
  pose proof (real_plus_comm (real_mult k (real_mult G e)) e) as H3.
  pose proof (igr_ring_step_b k G e) as H4.
  apply (real_eq_trans
           (real_plus (real_mult k (real_plus (real_mult (powb_pow k m) KL0)
                                              (real_mult G e)))
                      e)
           (real_plus (real_mult k (real_mult (powb_pow k m) KL0))
                      (real_plus (real_mult k (real_mult G e)) e))
           (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                      (real_mult (real_plus real_one (real_mult k G)) e))).
  - exact H1.
  - apply (real_eq_trans
             (real_plus (real_mult k (real_mult (powb_pow k m) KL0))
                        (real_plus (real_mult k (real_mult G e)) e))
             (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                        (real_plus (real_mult k (real_mult G e)) e))
             (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                        (real_mult (real_plus real_one (real_mult k G)) e))).
    + exact (RealSetoid.real_eq_plus_compat
                (real_mult k (real_mult (powb_pow k m) KL0))
                (real_plus (real_mult k (real_mult G e)) e)
                (real_mult (real_mult k (powb_pow k m)) KL0)
                (real_plus (real_mult k (real_mult G e)) e)
                H2
                (real_eq_refl (real_plus (real_mult k (real_mult G e)) e))).
    + apply (real_eq_trans
               (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                          (real_plus (real_mult k (real_mult G e)) e))
               (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                          (real_plus e (real_mult k (real_mult G e))))
               (real_plus (real_mult (real_mult k (powb_pow k m)) KL0)
                          (real_mult (real_plus real_one (real_mult k G)) e))).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_plus (real_mult k (real_mult G e)) e)
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_plus e (real_mult k (real_mult G e)))
                  (real_eq_refl (real_mult (real_mult k (powb_pow k m)) KL0))
                  H3).
      * exact (RealSetoid.real_eq_plus_compat
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_plus e (real_mult k (real_mult G e)))
                  (real_mult (real_mult k (powb_pow k m)) KL0)
                  (real_mult (real_plus real_one (real_mult k G)) e)
                  (real_eq_refl (real_mult (real_mult k (powb_pow k m)) KL0))
                  (real_eq_sym (real_mult (real_plus real_one (real_mult k G)) e)
                               (real_plus e (real_mult k (real_mult G e))) H4)).
Qed.

(* 0 < d ⟹ x < x + d（加零换形链，全已核基座件） *)
Lemma igr_lt_plus_r : forall (x d : Real),
  real_lt real_zero d -> real_lt x (real_plus x d).
Proof.
  intros x d Hd.
  pose proof (real_lt_plus_compat_lt_le real_zero d x x Hd (real_le_refl x)) as H0.
  pose proof (real_eq_lt_lt x (real_plus real_zero x) (real_plus d x)
                (real_eq_sym (real_plus real_zero x) x (kl_plus_zero_l x)) H0) as H1.
  exact (real_lt_eq_lt x (real_plus d x) (real_plus x d) H1
           (real_plus_comm d x)).
Qed.

(* 0 < d ⟹ x <= x + d *)
Lemma igr_le_plus_r : forall (x d : Real),
  real_lt real_zero d -> real_le x (real_plus x d).
Proof.
  intros x d Hd.
  exact (kl_le_eq_l (real_plus x real_zero) (real_plus x d) x           (real_le_plus_compat x x real_zero d (real_le_refl x)              (kl_lt_le_bridge real_zero d Hd))           (real_plus_zero x)).
Qed.

(* ========== W5：单步无假设收缩（实例化消解件 × 轨道站闭合） ========== *)

(* KL(pi*||pi_{t+1}) <= kappa·KL(pi*||pi_t) + eps（real_le 形）。
   S05 抽象层 policy_iter_kl_geom_step（S05_AlignmentGRPO.v:4436）的
   Real 层 eps 化同构件：接口假设 step_kl_eta_bound 的两个承载参数位
   在轨道上自足——HZ-参数位 := geodi_zpos（非平凡前提 NatLt 0 n 的
   Set 层编码，id_false_true 爆破先例 UpReqGeomIter.v:119），
   Hqv-参数位 := geodi_next_pos（与 HZ-参数位同字面项烘焙）。 *)
Theorem igr_geom_step_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S t) i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S t) i)))
    (real_plus
       (real_mult (igr_kappa eta)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i)
               (geodi_iterate n r Hr eta p Hp Hn t i)
               (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i))))
       eps).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  unfold geodi_iterate, geodi_iterate_pos.
  cbn [geodi_seq].
  destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn t) as [q Hq] eqn:Em.
  pose proof (geodi_seq_norm_pair n r Hr (real_plus real_one (real_opp eta)) p Hp Hn Hnormp t q Hq Em)
    as HnormQ.
  unfold geod_lsum in HnormQ.
  (* S15 原生实例化消解件换向实例：p-参数位 := r（pi*），r-参数位 := q（pi_t），eta-参数位 := kappa。
     换向后 KL(pi*||next) <= kappa·KL(pi*||pi_t) + eta·eps。 *)
  pose proof (real_step_kl_eta_bound_eps n r q (igr_kappa eta) Hr Hq
                Hnormr HnormQ
                (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn)
                (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn)
                (geod_kappa_pos eta Hlt1) (geod_kappa_le_one eta Heta)
                (real_mult eta eps)
                (real_mult_positive eta eps Heta Heps)) as Hstep.
  (* eta·eps <= eps（eta <= 1 乘法保序 + 1·eps == eps 换形） *)
  pose proof (kl_le_eq_r (real_mult eta eps) (real_mult real_one eps) eps
                (real_le_mult_compat_weak eta real_one eps
                   (kl_lt_le_bridge real_zero eps Heps)
                   (kl_lt_le_bridge eta real_one Hlt1))
                (kl_mult_one_l eps)) as Hscale.
  pose proof (real_le_plus_compat
                (real_mult (igr_kappa eta)
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                      (List.seq 0 n)))
                (real_mult (igr_kappa eta)
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                      (List.seq 0 n)))
                (real_mult eta eps) eps
                (real_le_refl
                   (real_mult (igr_kappa eta)
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                         (List.seq 0 n)))) Hscale) as Hle2.
  exact (real_le_trans _ _ _ Hstep Hle2).
Qed.

(* W5 Bishop 形（锐利）：KL(pi*||pi_{t+1}) <=_B kappa·KL(pi*||pi_t)。
   real_le_closure_b_one（UpRealLeB.v:381）一发闭合——逐 d 喂
   igr_geom_step_eps（实例化消解件 eps-参数位任意正预算）。 *)
Theorem igr_geom_step_discharged_B :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S t) i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S t) i)))
    (real_mult (igr_kappa eta)
       (geod_lsum n (fun i : nat =>
          real_kl_term (r i)
            (geodi_iterate n r Hr eta p Hp Hn t i)
            (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t.
  exact (real_le_closure_b_one _ _
    (fun d Hd => igr_geom_step_eps n r Hr eta Heta Hlt1 p Hp
                   Hnormr Hnormp Hn t d Hd)).
Qed.

(* ========== W6 前置：误差账的序性质 ========== *)

(* G_m >= 0（kappa >= 0 前提下沿递归保） *)
Lemma igr_gsum_nonneg : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (m : nat),
  real_le real_zero (igr_gsum (igr_kappa eta) m).
Proof.
  intros eta Heta Hlt1 m. induction m as [| m IH].
  - exact (real_le_refl real_zero).
  - pose proof (kl_lt_le_bridge real_zero (igr_kappa eta)
                  (geod_kappa_pos eta Hlt1)) as Hkle.
    pose proof (real_le_mult_compat_weak real_zero (igr_kappa eta)
                  (igr_gsum (igr_kappa eta) m) IH Hkle) as Hm0.
    pose proof (kl_le_eq_l (real_mult real_zero (igr_gsum (igr_kappa eta) m))
                  (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                  real_zero Hm0 (igr_mult_zero_r (igr_gsum (igr_kappa eta) m))) as HkG.
    exact (kl_le_eq_l (real_plus real_zero real_zero)
             (real_plus real_one (real_mult (igr_kappa eta)
                               (igr_gsum (igr_kappa eta) m)))
             real_zero
             (real_le_plus_compat real_zero real_one real_zero
                (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                (kl_lt_le_bridge real_zero real_one real_lt_zero_one) HkG)
             kl_zero_plus_zero).
Qed.

(* G_{S m} > 0（B 完成器的 D 正性证书；1 > 0 严格项 + kappa·G_m >= 0） *)
Lemma igr_gsum_S_pos : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (m : nat),
  real_lt real_zero (igr_gsum (igr_kappa eta) (Datatypes.S m)).
Proof.
  intros eta Heta Hlt1 m.
  pose proof (kl_lt_le_bridge real_zero (igr_kappa eta)
                (geod_kappa_pos eta Hlt1)) as Hkle.
  pose proof (igr_gsum_nonneg eta Heta Hlt1 m) as Hg0.
  pose proof (real_le_mult_compat_weak real_zero (igr_kappa eta)
                (igr_gsum (igr_kappa eta) m) Hg0 Hkle) as Hm0.
  pose proof (kl_le_eq_l (real_mult real_zero (igr_gsum (igr_kappa eta) m))
                (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                real_zero Hm0 (igr_mult_zero_r (igr_gsum (igr_kappa eta) m))) as HkG.
  exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
           (real_plus real_one (real_mult (igr_kappa eta)
                             (igr_gsum (igr_kappa eta) m)))
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              kl_zero_plus_zero)
           (real_lt_plus_compat_lt_le real_zero real_one real_zero
              (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
              real_lt_zero_one HkG)).
Qed.

(* G_t <= t·1（简化账的桥：kappa <= 1 折扣不增账） *)
Lemma igr_gsum_le_nmul : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (t : nat),
  real_le (igr_gsum (igr_kappa eta) t) (igr_nmul t real_one).
Proof.
  intros eta Heta Hlt1 t. induction t as [| m IH].
  - exact (real_le_refl real_zero).
  - pose proof (geod_kappa_le_one eta Heta) as Hkle.
    pose proof (real_le_mult_compat_weak (igr_kappa eta) real_one
                  (igr_gsum (igr_kappa eta) m)
                  (igr_gsum_nonneg eta Heta Hlt1 m) Hkle) as Hdisc.
    pose proof (kl_le_eq_r (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
                  (real_mult real_one (igr_gsum (igr_kappa eta) m))
                  (igr_gsum (igr_kappa eta) m) Hdisc
                  (kl_mult_one_l (igr_gsum (igr_kappa eta) m))) as Hdisc2.
    pose proof (real_le_trans _ _ _ Hdisc2 IH) as Hstep2.
    exact (real_le_plus_compat real_one real_one
             (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m))
             (igr_nmul m real_one) (real_le_refl real_one) Hstep2).
Qed.

(* (t·1)·eps == t·eps（nmul 对 one-系数的分配循环依赖清单） *)
Lemma igr_nmul_mult_one : forall (t : nat) (eps : Real),
  real_eq (real_mult (igr_nmul t real_one) eps) (igr_nmul t eps).
Proof.
  intros t eps. induction t as [| m IH].
  - exact (igr_mult_zero_r eps).
  - cbn [igr_nmul].
    exact (real_eq_trans
             (real_mult (real_plus real_one (igr_nmul m real_one)) eps)
             (real_plus (real_mult real_one eps) (real_mult (igr_nmul m real_one) eps))
             (real_plus eps (igr_nmul m eps))
             (igr_distrib_r real_one (igr_nmul m real_one) eps)
             (RealSetoid.real_eq_plus_compat
                (real_mult real_one eps) (real_mult (igr_nmul m real_one) eps)
                eps (igr_nmul m eps)
                (kl_mult_one_l eps)
                IH)).
Qed.

(* ========== W6 主件：迭代真几何率 ========== *)

(* 锐利几何和账（real_le 形）：
   KL(pi*||pi_t) <= (1-eta)^t·KL(pi*||pi_0) + (sum_{i<t}(1-eta)^i)·eps。
   归纳步喂全额 eps，循环依赖清单 igr_ring_step 一件闭合（免几何和恒等式）。 *)
Theorem igr_iter_geom_rate_tight_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (real_mult (igr_gsum (igr_kappa eta) t) eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  induction t as [| m IH].
  - (* t = 0：KL_0 <= 1·KL_0 + 0·eps（eq 支：0·eps == 0 循环依赖清单） *)
    apply (RealSetoid.real_le_id_l
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                (List.seq 0 n))
             (real_mult real_one
                (real_list_sum nat
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                   (List.seq 0 n)))
             (real_plus
                (real_mult real_one
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult real_zero eps))).
    + exact (real_eq_sym
                (real_mult real_one
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_list_sum nat
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                   (List.seq 0 n))
                (kl_mult_one_l
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))).
    + exact (inr
                (real_eq_trans
                   (real_mult real_one
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_plus
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      real_zero)
                   (real_plus
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult real_zero eps))
                   (real_eq_sym
                      (real_plus
                         (real_mult real_one
                            (real_list_sum nat
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                               (List.seq 0 n)))
                         real_zero)
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_plus_zero
                         (real_mult real_one
                            (real_list_sum nat
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                               (List.seq 0 n)))))
                   (RealSetoid.real_eq_plus_compat
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      real_zero
                      (real_mult real_one
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult real_zero eps)
                      (real_eq_refl
                         (real_mult real_one
                            (real_list_sum nat
                               (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                               (List.seq 0 n))))
                      (real_eq_sym (real_mult real_zero eps) real_zero
                         (igr_mult_zero_r eps))))).
  - (* t = S m：对子消解 + 实例化消解件全额喂定 + kappa 加权 IH + 总循环依赖清单 *)
    cbn [powb_pow igr_gsum].
    unfold geodi_iterate, geodi_iterate_pos in IH.
    unfold geodi_iterate, geodi_iterate_pos.
    revert IH.
    cbn [geodi_seq].
    destruct (geodi_seq n r Hr (real_plus real_one (real_opp eta)) p Hp Hn m) as [q Hq] eqn:Em.
    intro IH.
    pose proof (geodi_seq_norm_pair n r Hr (real_plus real_one (real_opp eta)) p Hp Hn Hnormp m q Hq Em)
      as HnormQ.
    unfold geod_lsum in HnormQ.
    (* S15 原生实例化消解件换向实例（同 W5，全额 eps 喂定） *)
    pose proof (real_step_kl_eta_bound_eps n r q (igr_kappa eta) Hr Hq
                  Hnormr HnormQ
                  (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn)
                  (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn)
                  (geod_kappa_pos eta Hlt1) (geod_kappa_le_one eta Heta)
                  eps Heps) as Hstep.
    (* IH 的 kappa 加权（严格正左因子，UpReqGeomIter.v:330 件） *)
    pose proof (geodi_mult_le_compat_l (igr_kappa eta)
                  (real_list_sum nat
                     (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                     (List.seq 0 n))
                  (real_plus
                     (real_mult (powb_pow (igr_kappa eta) m)
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) m) eps))
                  (geod_kappa_pos eta Hlt1) IH) as Hmul.
    pose proof (real_le_plus_compat
                  (real_mult (igr_kappa eta)
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                        (List.seq 0 n)))
                  (real_mult (igr_kappa eta)
                     (real_plus
                        (real_mult (powb_pow (igr_kappa eta) m)
                           (real_list_sum nat
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                              (List.seq 0 n)))
                        (real_mult (igr_gsum (igr_kappa eta) m) eps)))
                  eps eps
                  Hmul (real_le_refl eps)) as Hmid.
    pose proof (real_le_trans
                  (real_list_sum nat
                     (fun i : nat =>
                        real_kl_term (r i)
                          (real_step_next n r q (igr_kappa eta) Hr Hq
                             (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn) i)
                          (Hr i)
                          (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn i))
                     (List.seq 0 n))
                  (real_plus
                     (real_mult (igr_kappa eta)
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (q i) (Hr i) (Hq i))
                           (List.seq 0 n)))
                     eps)
                  (real_plus
                     (real_mult (igr_kappa eta)
                        (real_plus
                           (real_mult (powb_pow (igr_kappa eta) m)
                              (real_list_sum nat
                                 (fun i : nat =>
                                    real_kl_term (r i) (p i) (Hr i) (Hp i))
                                 (List.seq 0 n)))
                           (real_mult (igr_gsum (igr_kappa eta) m) eps)))
                     eps)
                  Hstep Hmid) as Hchain.
    exact (kl_le_eq_r
             (real_list_sum nat
                (fun i : nat =>
                   real_kl_term (r i)
                     (real_step_next n r q (igr_kappa eta) Hr Hq
                        (geodi_zpos n r q (igr_kappa eta) Hr Hq Hn) i)
                     (Hr i)
                     (geodi_next_pos n r q (igr_kappa eta) Hr Hq Hn i))
                (List.seq 0 n))
             (real_plus
                (real_mult (igr_kappa eta)
                   (real_plus
                      (real_mult (powb_pow (igr_kappa eta) m)
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult (igr_gsum (igr_kappa eta) m) eps)))
                eps)
             (real_plus
                (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult
                   (real_plus real_one
                      (real_mult (igr_kappa eta) (igr_gsum (igr_kappa eta) m)))
                   eps))
             Hchain
             (igr_ring_step (igr_kappa eta)
                (real_list_sum nat
                   (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                   (List.seq 0 n))
                (igr_gsum (igr_kappa eta) m) eps m)).
Qed.

(* B 形闭合 t=0 支共用：KL_0 <=_B 1·KL_0 + z（z 为任意零形误差参数位） *)
Lemma igr_B_zero : forall (KL0 z : Real),
  real_eq z real_zero ->
  real_le_b KL0 (real_plus (real_mult real_one KL0) z).
Proof.
  intros KL0 z Hz. unfold real_le_b. intros d Hd.
  pose proof (igr_lt_plus_r KL0 d Hd) as Hlt.
  pose proof (real_eq_sym
                (real_plus (real_mult real_one KL0) (real_plus z d))
                (real_plus (real_plus (real_mult real_one KL0) z) d)
                (real_plus_assoc (real_mult real_one KL0) z d)) as Heq1.
  pose proof (real_eq_trans
                (real_plus (real_plus (real_mult real_one KL0) z) d)
                (real_plus (real_mult real_one KL0) (real_plus z d))
                (real_plus KL0 d)
                Heq1
                (RealSetoid.real_eq_plus_compat
                   (real_mult real_one KL0)
                   (real_plus z d)
                   KL0 d
                   (kl_mult_one_l KL0)
                   (real_eq_trans (real_plus z d) (real_plus real_zero d) d
                      (RealSetoid.real_eq_plus_compat z d real_zero d
                         Hz (real_eq_refl d))
                      (kl_plus_zero_l d)))) as Heq.
  exact (real_lt_eq_lt KL0 (real_plus KL0 d)
           (real_plus (real_plus (real_mult real_one KL0) z) d)
           Hlt (real_eq_sym _ _ Heq)).
Qed.

(* 锐利几何和账（Bishop 形）：
   KL(pi*||pi_t) <=_B (1-eta)^t·KL(pi*||pi_0) + (sum_{i<t}(1-eta)^i)·eps。
   t>=1 支由 real_le_closure_b（D := G_t，正性证书 igr_gsum_S_pos）
   一发闭合；t=0 支环换形（igr_B_zero）。 *)
Theorem igr_iter_geom_rate_tight :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (real_mult (igr_gsum (igr_kappa eta) t) eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  destruct t as [| m].
  - exact (igr_B_zero
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                (List.seq 0 n)) (real_mult real_zero eps)
             (igr_mult_zero_r eps)).
  - apply (real_le_closure_b
             (real_list_sum nat
                (fun i : nat =>
                   real_kl_term (r i)
                     (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                     (Hr i)
                     (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
                (List.seq 0 n))
             (real_plus
                (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
             (igr_gsum (igr_kappa eta) (Datatypes.S m))
             (igr_gsum_S_pos eta Heta Hlt1 m)).
    intros e He.
    pose proof (real_lt_plus_compat real_zero eps real_zero e Heps He) as Hpe0.
    pose proof (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus eps e)
                  (real_eq_sym (real_plus real_zero real_zero) real_zero
                     kl_zero_plus_zero) Hpe0) as Hpe.
    pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                  Hnormr Hnormp Hn (Datatypes.S m) (real_plus eps e) Hpe) as Ht.
    pose proof (igr_distrib_l (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps e)
      as Hd1.
    pose proof (kl_eq_le_bridge
                  (real_plus
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_plus eps e)))
                  (real_plus
                     (real_plus
                        (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                           (real_list_sum nat
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                              (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
                  (real_eq_trans
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                      (real_plus eps e)))
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_plus
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e)))
                (real_plus
                   (real_plus
                      (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n)))
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
                (RealSetoid.real_eq_plus_compat
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                      (real_plus eps e))
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_plus
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                      (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
                   (real_eq_refl
                      (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n))))
                   Hd1)
                (real_plus_assoc
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e)))) as Hbridge.
    exact (real_le_trans
             (real_list_sum nat
                (fun i : nat =>
                   real_kl_term (r i)
                     (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                     (Hr i)
                     (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
                (List.seq 0 n))
             (real_plus
                (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                   (real_list_sum nat
                      (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                      (List.seq 0 n)))
                (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                   (real_plus eps e)))
             (real_plus
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
             (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) e))
             Ht Hbridge).
Qed.

(* t·eps 简化账（real_le 形）：从锐利账放缩 G_t <= t·1。 *)
Theorem igr_iter_geom_rate_eps :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (igr_nmul t eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                Hnormr Hnormp Hn t eps Heps) as Htight.
  (* G_t·eps <= (t·1)·eps == t·eps *)
  pose proof (real_le_mult_compat_weak (igr_gsum (igr_kappa eta) t)
                (igr_nmul t real_one) eps
                (kl_lt_le_bridge real_zero eps Heps)
                (igr_gsum_le_nmul eta Heta Hlt1 t)) as Hsc.
  pose proof (kl_le_eq_r (real_mult (igr_gsum (igr_kappa eta) t) eps)
                (real_mult (igr_nmul t real_one) eps) (igr_nmul t eps)
                Hsc (igr_nmul_mult_one t eps)) as Hsc2.
  exact (real_le_trans _ _ _ Htight
           (real_le_plus_compat
              (real_mult (powb_pow (igr_kappa eta) t)
                 (real_list_sum nat
                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (List.seq 0 n)))
              (real_mult (powb_pow (igr_kappa eta) t)
                 (real_list_sum nat
                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (List.seq 0 n)))
              (real_mult (igr_gsum (igr_kappa eta) t) eps) (igr_nmul t eps)
              (real_le_refl
                 (real_mult (powb_pow (igr_kappa eta) t)
                    (real_list_sum nat
                       (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                       (List.seq 0 n))))
              Hsc2)).
Qed.

(* t·eps 简化账（Bishop 形）：t>=1 支经锐利账 + 逆元预算换形
   （G_{S m}·(eps + d·inv G_{S m}) == G_{S m}·eps + d），t=0 支环换形。 *)
Theorem igr_iter_geom_rate :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (igr_nmul t eps)).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn t eps Heps.
  unfold geod_lsum in *.
  destruct t as [| m].
  - unfold geodi_iterate, geodi_iterate_pos.
    cbn [geodi_seq projT1 projT2 powb_pow igr_nmul].
    exact (igr_B_zero
             (real_list_sum nat
                (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                (List.seq 0 n)) real_zero (real_eq_refl real_zero)).
  - (* S m 支：G_{S m} > 0，预算 e := eps + d·inv(G_{S m}) *)
    pose proof (igr_gsum_S_pos eta Heta Hlt1 m) as HgG.
    apply real_le_closure_b_one. intros d Hd.
    pose proof
      (real_mult_positive d
         (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)
         Hd (real_inv_pos_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) as Hdi.
    pose proof (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                  (real_plus eps
                     (real_mult d
                        (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                  (real_eq_sym (real_plus real_zero real_zero) real_zero
                     kl_zero_plus_zero)
                  (real_lt_plus_compat_lt_le real_zero eps real_zero
                     (real_mult d
                        (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                     Heps
                     (kl_lt_le_bridge real_zero
                        (real_mult d
                           (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                        Hdi))) as Hbudget.
    pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                  Hnormr Hnormp Hn (Datatypes.S m)
                  (real_plus eps
                     (real_mult d
                        (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                  Hbudget) as Htight.
    (* 换形：G·(eps + d·invG) == G·eps + d *)
    pose proof (igr_distrib_l (igr_gsum (igr_kappa eta) (Datatypes.S m))
                  eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))) as Hd1.
    pose proof (RealSetoid.real_eq_mult_compat
                  (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                  (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_mult (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d)
                  (real_eq_refl (igr_gsum (igr_kappa eta) (Datatypes.S m)))
                  (real_mult_comm d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))) as Hd2.
    pose proof (igr_ring_reassoc (igr_gsum (igr_kappa eta) (Datatypes.S m))
                  (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d) as Hd3.
    pose proof (RealSetoid.real_eq_mult_compat
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) d
                  real_one d
                  (real_inv_pos_correct (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)
                  (real_eq_refl d)) as Hd4.
    pose proof (kl_mult_one_l d) as Hd5.
    pose proof (real_eq_trans
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                     (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d)
                  Hd1
                  (RealSetoid.real_eq_plus_compat
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d
                     (real_eq_refl
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                     (real_eq_trans
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                           (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                           (real_mult (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d))
                        d
                        Hd2
                        (real_eq_trans
                           (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                              (real_mult (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG) d))
                           (real_mult
                              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                                 (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) d)
                           d
                           Hd3
                           (real_eq_trans
                              (real_mult
                                 (real_mult
                                    (igr_gsum (igr_kappa eta) (Datatypes.S m)) (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) d)
                              (real_mult real_one d)
                              d
                              Hd4
                              Hd5))))) as Hsc.
    (* 链：KL <= A + G·(eps + d·invG) == (A + G·eps) + d <= (A + t·eps) + d *)
    pose proof (RealSetoid.real_eq_plus_compat
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                     (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d)
                  (real_eq_refl
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n))))
                  Hsc) as HeqA.
    pose proof (real_plus_assoc
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                  d) as HeqB.
    pose proof (real_le_trans
                  (real_list_sum nat
                     (fun i : nat =>
                        real_kl_term (r i)
                          (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                          (Hr i)
                          (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
                     (List.seq 0 n))
                  (real_plus
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n)))
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                        (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
                  (real_plus
                     (real_plus
                        (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                           (real_list_sum nat
                              (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                              (List.seq 0 n)))
                        (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                     d)
                  Htight
                  (kl_eq_le_bridge _ _
                     (real_eq_trans
                        (real_plus
                           (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                              (real_list_sum nat
                                 (fun i : nat =>
                                    real_kl_term (r i) (p i) (Hr i) (Hp i))
                                 (List.seq 0 n)))
                           (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                              (real_plus eps (real_mult d (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
                        (real_plus
                           (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                              (real_list_sum nat
                                 (fun i : nat =>
                                    real_kl_term (r i) (p i) (Hr i) (Hp i))
                                 (List.seq 0 n)))
                           (real_plus
                              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                              d))
                        (real_plus
                           (real_plus
                              (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                                 (real_list_sum nat
                                    (fun i : nat =>
                                       real_kl_term (r i) (p i) (Hr i) (Hp i))
                                    (List.seq 0 n)))
                              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                           d)
                        HeqA HeqB))) as Hch1.
    pose proof (real_le_mult_compat_weak (igr_gsum (igr_kappa eta) (Datatypes.S m))
                  (igr_nmul (Datatypes.S m) real_one) eps
                  (kl_lt_le_bridge real_zero eps Heps)
                  (igr_gsum_le_nmul eta Heta Hlt1 (Datatypes.S m))) as Hsc2.
    pose proof (kl_le_eq_r
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                  (real_mult (igr_nmul (Datatypes.S m) real_one) eps)
                  (igr_nmul (Datatypes.S m) eps)
                  Hsc2 (igr_nmul_mult_one (Datatypes.S m) eps)) as Hsc3.
    exact (real_le_trans _ _ _ Hch1
             (real_le_plus_compat
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                (real_plus
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (igr_nmul (Datatypes.S m) eps))
                d d
                (real_le_plus_compat
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                      (real_list_sum nat
                         (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                         (List.seq 0 n)))
                   (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                   (igr_nmul (Datatypes.S m) eps)
                   (real_le_refl
                      (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                         (real_list_sum nat
                            (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                            (List.seq 0 n))))
                   Hsc3)
                (real_le_refl d))).
Qed.

(* ============================================================ *)
(* R2·④L（I4 缺口④可行特化）：严格正左因子 le_b 乘法保序                *)
(*   a ≤_B b ∧ 0 < c ⟹ c·a ≤_B c·b。预算 e·inv(c) 字面现形——            *)
(*   尾注缺口④的非严格右因子需 KL₀ 精确非负（在案障碍），本特化绕开：  *)
(*   除法可行（c 严格正），新数学面，库内无同形件。                      *)
(* ============================================================ *)
Lemma igr_le_b_mult_l : forall (a b c : Real),
  real_le_b a b -> real_lt real_zero c -> real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hab Hc. unfold real_le_b. intros e He.
  pose proof (real_mult_positive e (real_inv_pos c Hc) He
                 (real_inv_pos_pos c Hc)) as Hdic.
  pose proof (Hab (real_mult e (real_inv_pos c Hc)) Hdic) as Hlt.
  pose proof (real_mult_lt_compat_l a
                 (real_plus b (real_mult e (real_inv_pos c Hc))) c Hlt Hc) as Hlt2.
  pose proof (real_eq_trans
                 (real_mult c (real_mult e (real_inv_pos c Hc)))
                 (real_mult c (real_mult (real_inv_pos c Hc) e))
                 e
                 (RealSetoid.real_eq_mult_compat c (real_mult e (real_inv_pos c Hc)) c
                    (real_mult (real_inv_pos c Hc) e) (real_eq_refl c)
                    (real_mult_comm e (real_inv_pos c Hc)))
                 (real_eq_trans
                    (real_mult c (real_mult (real_inv_pos c Hc) e))
                    (real_mult (real_mult c (real_inv_pos c Hc)) e)
                    e
                    (igr_ring_reassoc c (real_inv_pos c Hc) e)
                    (real_eq_trans
                       (real_mult (real_mult c (real_inv_pos c Hc)) e)
                       (real_mult real_one e)
                       e
                       (RealSetoid.real_eq_mult_compat
                          (real_mult c (real_inv_pos c Hc)) e real_one e
                          (real_inv_pos_correct c Hc) (real_eq_refl e))
                       (kl_mult_one_l e)))) as Hring.
  pose proof (igr_distrib_l c b (real_mult e (real_inv_pos c Hc))) as Hdd.
  pose proof (real_lt_eq_lt (real_mult c a)
                (real_mult c (real_plus b (real_mult e (real_inv_pos c Hc))))
                (real_plus (real_mult c b) (real_mult c (real_mult e (real_inv_pos c Hc))))
                Hlt2 Hdd) as Hlt3.
  exact (real_lt_eq_lt (real_mult c a)
           (real_plus (real_mult c b) (real_mult c (real_mult e (real_inv_pos c Hc))))
           (real_plus (real_mult c b) e)
           Hlt3
           (RealSetoid.real_eq_plus_compat (real_mult c b)
              (real_mult c (real_mult e (real_inv_pos c Hc)))
              (real_mult c b) e
              (real_eq_refl (real_mult c b)) Hring)).
Qed.

(* ============================================================ *)
(* R2·幂上界精确肢（④L 与见证器的依存件；库内 PowB 仅 B 形）            *)
(* ============================================================ *)
Lemma igr_powb_nonneg : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (t : nat),
  real_le real_zero (powb_pow (igr_kappa eta) t).
Proof.
  intros eta Heta Hlt1 t. induction t as [| m IH].
  - exact (kl_lt_le_bridge real_zero real_one real_lt_zero_one).
  - pose proof (kl_lt_le_bridge real_zero (igr_kappa eta)
                  (geod_kappa_pos eta Hlt1)) as Hk0.
    pose proof (real_le_mult_compat_weak real_zero (igr_kappa eta)
                  (powb_pow (igr_kappa eta) m) IH Hk0) as Hstep.
    exact (kl_le_eq_l (real_mult real_zero (powb_pow (igr_kappa eta) m))
             (real_mult (igr_kappa eta) (powb_pow (igr_kappa eta) m))
             real_zero Hstep
             (igr_mult_zero_r (powb_pow (igr_kappa eta) m))).
Qed.

Lemma igr_powb_le_one : forall (eta : Real) (Heta : real_lt real_zero eta)
    (Hlt1 : real_lt eta real_one) (t : nat),
  real_le (powb_pow (igr_kappa eta) t) real_one.
Proof.
  intros eta Heta Hlt1 t. induction t as [| m IH].
  - cbn [powb_pow]. exact (real_le_refl real_one).
  - pose proof (real_le_mult_compat_weak (igr_kappa eta) real_one
                  (powb_pow (igr_kappa eta) m)
                  (igr_powb_nonneg eta Heta Hlt1 m)
                  (geod_kappa_le_one eta Heta)) as Hdisc.
    pose proof (kl_le_eq_r (real_mult (igr_kappa eta) (powb_pow (igr_kappa eta) m))
                  (real_mult real_one (powb_pow (igr_kappa eta) m))
                  (powb_pow (igr_kappa eta) m)
                  Hdisc (kl_mult_one_l (powb_pow (igr_kappa eta) m))) as Hdisc2.
    exact (real_le_trans _ _ _ Hdisc2 IH).
Qed.

(* ============================================================ *)
(* R3·sigT 四层见证器（R2.2 遗留闭合：S 支拆分路线）                  *)
(*                                                              *)
(*   第一层 igr_ring_scale_inv：预算换形环件（独立单目标引理）          *)
(*     G·(e + d·invG) == G·e + d（invG 正性证书型）。                 *)
(*   第二层 igr_iter_budget_witness_S：S 站逐预算 real_le 链            *)
(*     （按 t=S m 特化的独立单目标引理——坑⑨：t 分派证明一律拆引理）。   *)
(*   第三层 igr_iter_geom_rate_witness：Defined 项级 match t 分派       *)
(*     （destruct 不可用于 Defined 项级——用 match），产出              *)
(*     「KL_t ≤_B κ^t·KL₀ + G_t·eps」的 Bishop 见证：real_le_b 展开    *)
(*     即 ∀d>0 的逐预算见证映射 f，real_lt 为 sigT——提取面即           *)
(*     eps↦(gap, N) 可计算映射。                                      *)
(*   第四层 igr_iter_geom_rate_witness_one：预算 d:=1 实形——            *)
(*     具体实例化的 real_lt sigT 值（提取面终品）。                    *)
(*                                                              *)
(* 公理面：零新增假设位；见证主件/实形件为 Defined（真可计算，          *)
(* 非 Qed 糊封）；支件 ring_scale_inv / budget_witness_S 为 Qed 闭合。  *)
(* 提取面组织：WALL-1 iface 别名 delta 伪影坑——接口桥接引理不进提取面，    *)
(* 见证器语句面素颜 geod_*/real_*（R1 六件提取 0 magic 同款组织）。     *)
(* ============================================================ *)

(* 第一层：预算换形环件。G 严格正（逆元证书随行），则
   G·(e + d·invG) == G·e + d——逆元预算 d 恰好脱账。 *)
Lemma igr_ring_scale_inv : forall (G : Real) (HG : real_lt real_zero G)
    (e d : Real),
  real_eq
    (real_mult G (real_plus e (real_mult d (real_inv_pos G HG))))
    (real_plus (real_mult G e) d).
Proof.
  intros G HG e d.
  pose proof (igr_distrib_l G e (real_mult d (real_inv_pos G HG))) as Hd1.
  pose proof (RealSetoid.real_eq_mult_compat G
                 (real_mult d (real_inv_pos G HG)) G
                 (real_mult (real_inv_pos G HG) d)
                 (real_eq_refl G)
                 (real_mult_comm d (real_inv_pos G HG))) as Hd2.
  pose proof (igr_ring_reassoc G (real_inv_pos G HG) d) as Hd3.
  pose proof (RealSetoid.real_eq_mult_compat
                 (real_mult G (real_inv_pos G HG)) d real_one d
                 (real_inv_pos_correct G HG) (real_eq_refl d)) as Hd4.
  pose proof (kl_mult_one_l d) as Hd5.
  exact (real_eq_trans
           (real_mult G (real_plus e (real_mult d (real_inv_pos G HG))))
           (real_plus (real_mult G e)
              (real_mult G (real_mult d (real_inv_pos G HG))))
           (real_plus (real_mult G e) d)
           Hd1
           (RealSetoid.real_eq_plus_compat
              (real_mult G e)
              (real_mult G (real_mult d (real_inv_pos G HG)))
              (real_mult G e) d
              (real_eq_refl (real_mult G e))
              (real_eq_trans
                 (real_mult G (real_mult d (real_inv_pos G HG)))
                 (real_mult G (real_mult (real_inv_pos G HG) d))
                 d
                 Hd2
                 (real_eq_trans
                    (real_mult G (real_mult (real_inv_pos G HG) d))
                    (real_mult (real_mult G (real_inv_pos G HG)) d)
                    d
                    Hd3
                    (real_eq_trans
                       (real_mult (real_mult G (real_inv_pos G HG)) d)
                       (real_mult real_one d)
                       d
                       Hd4
                       Hd5))))).
Qed.

(* 第二层：S 站逐预算 real_le 链（单目标，t 已特化 S m——坑⑨拆分）：
   KL_{S m} <= (κ^{S m}·KL₀ + G_{S m}·eps) + d（内预算 e := eps + d·invG
   喂锐利账后环件脱账）。 *)
Lemma igr_iter_budget_witness_S :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (m : nat) (eps : Real) (Heps : real_lt real_zero eps)
    (d : Real) (Hd : real_lt real_zero d),
  real_le
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i)))
    (real_plus
       (real_plus
          (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
             (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i))))
          (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
       d).
Proof.
  intros n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn m eps Heps d Hd.
  unfold geod_lsum in *.
  pose proof (igr_gsum_S_pos eta Heta Hlt1 m) as HgG.
  pose proof (real_mult_positive d
                 (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)
                 Hd
                 (real_inv_pos_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)) as Hdi.
  pose proof (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                 (real_plus eps
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                 (real_eq_sym (real_plus real_zero real_zero) real_zero
                    kl_zero_plus_zero)
                 (real_lt_plus_compat_lt_le real_zero eps real_zero
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                    Heps
                    (kl_lt_le_bridge real_zero
                       (real_mult d
                          (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))
                       Hdi))) as Hbudget.
  pose proof (igr_iter_geom_rate_tight_eps n r Hr eta Heta Hlt1 p Hp
                 Hnormr Hnormp Hn (Datatypes.S m)
                 (real_plus eps
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))
                 Hbudget) as Htight.
  pose proof (igr_ring_scale_inv
                 (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG eps d) as Hsc.
  pose proof (RealSetoid.real_eq_plus_compat
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                     (real_plus eps
                        (real_mult d
                           (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG))))
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_plus
                     (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                     d)
                  (real_eq_refl
                     (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                        (real_list_sum nat
                           (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                           (List.seq 0 n))))
                  Hsc) as HeqA.
  pose proof (real_plus_assoc
                  (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                     (real_list_sum nat
                        (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                        (List.seq 0 n)))
                  (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                  d) as HeqB.
  exact (real_le_trans
           (real_list_sum nat
              (fun i : nat =>
                 real_kl_term (r i)
                   (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
                   (Hr i)
                   (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i))
              (List.seq 0 n))
           (real_plus
              (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                 (real_list_sum nat
                    (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                    (List.seq 0 n)))
              (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                 (real_plus eps
                    (real_mult d
                       (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
           (real_plus
              (real_plus
                 (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                    (real_list_sum nat
                       (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                       (List.seq 0 n)))
                 (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
              d)
           Htight
           (kl_eq_le_bridge _ _
              (real_eq_trans
                 (real_plus
                    (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                       (real_list_sum nat
                          (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                          (List.seq 0 n)))
                    (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m))
                       (real_plus eps
                          (real_mult d
                             (real_inv_pos (igr_gsum (igr_kappa eta) (Datatypes.S m)) HgG)))))
                 (real_plus
                    (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                       (real_list_sum nat
                          (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                          (List.seq 0 n)))
                    (real_plus
                       (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps)
                       d))
                 (real_plus
                    (real_plus
                       (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
                          (real_list_sum nat
                             (fun i : nat => real_kl_term (r i) (p i) (Hr i) (Hp i))
                             (List.seq 0 n)))
                       (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
                    d)
                 HeqA HeqB))).
Qed.

(* 第三层：见证主件（Defined 项级 match t 分派——坑⑨：支件已拆独立
   引理，本件零证明、纯项级装配）。 *)
Definition igr_iter_geom_rate_witness :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_le_b
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_mult (powb_pow (igr_kappa eta) t)
          (geod_lsum n (fun i : nat =>
             real_kl_term (r i) (p i) (Hr i) (Hp i))))
       (real_mult (igr_gsum (igr_kappa eta) t) eps)) :=
  fun (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (t : nat) (eps : Real)
    (Heps : real_lt real_zero eps) =>
  match t as t0 return
    real_le_b
      (geod_lsum n (fun i : nat =>
         real_kl_term (r i)
           (geodi_iterate n r Hr eta p Hp Hn t0 i)
           (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t0 i)))
      (real_plus
         (real_mult (powb_pow (igr_kappa eta) t0)
            (geod_lsum n (fun i : nat =>
               real_kl_term (r i) (p i) (Hr i) (Hp i))))
         (real_mult (igr_gsum (igr_kappa eta) t0) eps))
    with
  | Datatypes.O =>
      igr_B_zero
        (geod_lsum n (fun i : nat =>
           real_kl_term (r i) (p i) (Hr i) (Hp i)))
        (real_mult real_zero eps)
        (igr_mult_zero_r eps)
  | Datatypes.S m =>
      real_le_closure_b_one
        (geod_lsum n (fun i : nat =>
           real_kl_term (r i)
             (geodi_iterate n r Hr eta p Hp Hn (Datatypes.S m) i)
             (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn (Datatypes.S m) i)))
        (real_plus
           (real_mult (powb_pow (igr_kappa eta) (Datatypes.S m))
              (geod_lsum n (fun i : nat =>
                 real_kl_term (r i) (p i) (Hr i) (Hp i))))
           (real_mult (igr_gsum (igr_kappa eta) (Datatypes.S m)) eps))
        (igr_iter_budget_witness_S n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn
           m eps Heps)
  end.

(* 第四层：d:=1 实形——预算取字面 1（证书 real_lt_zero_one 既有件），
   具体实例化的 real_lt sigT 值（提取面终品：eps↦(gap, N) 映射现形）。 *)
Definition igr_iter_geom_rate_witness_one :
  forall (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n)
    (t : nat) (eps : Real) (Heps : real_lt real_zero eps),
  real_lt
    (geod_lsum n (fun i : nat =>
       real_kl_term (r i)
         (geodi_iterate n r Hr eta p Hp Hn t i)
         (Hr i) (geodi_iterate_pos n r Hr eta p Hp Hn t i)))
    (real_plus
       (real_plus
          (real_mult (powb_pow (igr_kappa eta) t)
             (geod_lsum n (fun i : nat =>
                real_kl_term (r i) (p i) (Hr i) (Hp i))))
          (real_mult (igr_gsum (igr_kappa eta) t) eps))
       real_one) :=
  fun (n : nat) (r : nat -> Real)
    (Hr : forall i : nat, real_lt real_zero (r i))
    (eta : Real) (Heta : real_lt real_zero eta) (Hlt1 : real_lt eta real_one)
    (p : nat -> Real) (Hp : forall i : nat, real_lt real_zero (p i))
    (Hnormr : real_eq (geod_lsum n r) real_one)
    (Hnormp : real_eq (geod_lsum n p) real_one)
    (Hn : NatLt 0 n) (t : nat) (eps : Real)
    (Heps : real_lt real_zero eps) =>
  igr_iter_geom_rate_witness n r Hr eta Heta Hlt1 p Hp Hnormr Hnormp Hn
    t eps Heps real_one real_lt_zero_one.

(* ============================================================ *)
(*   igr_ 侧版本）。                                                    *)
(*                                                              *)
(*   Real 层 real_le 为 Or 编码（构造性不可判定），「最小 t」搜索的      *)
(*   可判定化取 Q 证书面：调用方供给 κ/KL₀/eps/target 的 Q 层证书，      *)
(*   测试在 Q 层精确可判定；igr_k_select 在 [0,H] 窗内枚举返回首个       *)
(* （=最小）通过站，None := 窗内无解。                                 *)
(*   接口对称性注记：与 C10 mix_k_select 同形（eps↦最小 t 的 Nat 枚举）  *)
(* ============================================================ *)

Fixpoint igr_qpow (q : Q) (t : nat) : Q :=
  match t with
  | Datatypes.O => 1%Q
  | Datatypes.S m => Qmult q (igr_qpow q m)
  end.

(* 窗内枚举：返回 [0,t] 内最小通过站（None := 无）。 *)
Fixpoint igr_k_enum (test : nat -> bool) (t : nat) : option nat :=
  match t with
  | Datatypes.O => if test Datatypes.O then Some Datatypes.O else None
  | Datatypes.S m =>
      match igr_k_enum test m with
      | Some k => Some k
      | None => if test (Datatypes.S m) then Some (Datatypes.S m) else None
      end
  end.

(* Q 层测试：κ^t·KL₀ + t·eps ≤ target（Q 证书面，精确可判定）。 *)
Definition igr_k_test (kq KL0q epsq targetq : Q) (t : nat) : bool :=
  Qle_bool (Qplus (Qmult (igr_qpow kq t) KL0q)
                  (Qmult (Qmake (Z.of_nat t) 1) epsq))
           targetq.

(* k-计算器：给定 Q 证书与搜索窗 H，Defined 返回最小通过站。 *)
Definition igr_k_select (kq KL0q epsq targetq : Q) (H : nat) : option nat :=
 igr_k_enum (igr_k_test kq KL0q epsq targetq) H.

(* 枚举可靠性：返回站必通过测试。 *)
Lemma igr_k_enum_sound : forall (test : nat -> bool) (t k : nat),
  igr_k_enum test t = Some k -> test k = true.
Proof.
  intros test t. induction t as [| m IH]; intros k Hk.
  - cbn [igr_k_enum] in Hk. destruct (test Datatypes.O) eqn:Ht0.
    + injection Hk. intros Hkk. rewrite <- Hkk. exact Ht0.
    + discriminate Hk.
  - cbn [igr_k_enum] in Hk.
    destruct (igr_k_enum test m) eqn:Em.
    + (* 内窗已解：destruct-eqn 已把 IH/Hk 消解为 Some n 形，同形直接代入 *)
      apply IH. exact Hk.
    + destruct (test (Datatypes.S m)) eqn:Ht.
      * injection Hk. intros Hkk. rewrite <- Hkk. exact Ht.
      * discriminate Hk.
Qed.

(* 枚举无解账：None ⟹ 窗内全不通过。 *)
Lemma igr_k_enum_none : forall (test : nat -> bool) (t : nat),
  igr_k_enum test t = None -> forall j : nat, j <= t -> test j = false.
Proof.
  intros test t. induction t as [| m IH]; intros Heq j Hj.
  - cbn [igr_k_enum] in Heq. destruct (test Datatypes.O) eqn:Ht0.
    + discriminate Heq.
    + apply (proj1 (Nat.lt_eq_cases j 0)) in Hj.
      destruct Hj as [Hlt0 | Heqj0].
      * exfalso. exact (Nat.nlt_0_r j Hlt0).
      * rewrite Heqj0. exact Ht0.
  - cbn [igr_k_enum] in Heq.
    destruct (igr_k_enum test m) eqn:Em.
    + discriminate Heq.
    + destruct (test (Datatypes.S m)) eqn:HtS.
      * discriminate Heq.
      * apply (proj1 (Nat.lt_eq_cases j (Datatypes.S m))) in Hj.
        destruct Hj as [Hlt | Heqj].
        -- exact (IH eq_refl j (proj1 (Nat.lt_succ_r j m) Hlt)).
        -- rewrite Heqj. exact HtS.
Qed.

(* 最小性：Some k ⟹ k 通过且 k 以下全不通过（真「最小」账）。 *)
Lemma igr_k_enum_min : forall (test : nat -> bool) (t k : nat),
  igr_k_enum test t = Some k ->
  forall j : nat, j < k -> test j = false.
Proof.
  intros test t. induction t as [| m IH]; intros k Hk j Hj.
  - cbn [igr_k_enum] in Hk. destruct (test Datatypes.O) eqn:Ht0.
    + injection Hk. intros Hkk. rewrite <- Hkk in Hj.
      exfalso. exact (Nat.nlt_0_r j Hj).
    + discriminate Hk.
  - cbn [igr_k_enum] in Hk.
    destruct (igr_k_enum test m) eqn:Em.
    + (* 内窗已解：destruct-eqn 已把 IH 消解为 Some n 形，直接承最小性 *)
      exact (IH k Hk j Hj).
    + destruct (test (Datatypes.S m)) eqn:Ht.
      * (* k = S m 站：j < S m ⟹ j <= m ⟹ 无解账 *)
        injection Hk. intros Hkk. rewrite <- Hkk in Hj.
        apply (proj1 (Nat.lt_succ_r j m)) in Hj.
        exact (igr_k_enum_none test m Em j Hj).
      * discriminate Hk.
Qed.

(* k-计算器主账：Some k ⟹ k 通过 ∧ 以下全不通过（单目标复合）。 *)
Lemma igr_k_select_min : forall (kq KL0q epsq targetq : Q) (H k : nat),
  igr_k_select kq KL0q epsq targetq H = Some k ->
  igr_k_test kq KL0q epsq targetq k = true /\
  (forall j : nat, j < k -> igr_k_test kq KL0q epsq targetq j = false).
Proof.
  intros kq KL0q epsq targetq H k Hsel.
  unfold igr_k_select in Hsel. split.
  - exact (igr_k_enum_sound _ _ _ Hsel).
  - exact (igr_k_enum_min _ _ _ Hsel).
Qed.

(* ============================================================ *)
(* 诚实登记表                                                    *)
(*                                                              *)
(* 【层级声明】本件全部语句在 Real 化离散分布层（geod_lsum/        *)
(*   real_kl_term 折叠和），与实例化消解件（S15:1014）同层；S05 抽象层    *)
(*   W3 领地，本件不等待、不重叠。                                *)
(*                                                              *)
(* 【锐利核算豁免】几何和恒等式 eta·G_t == 1 - kappa^t 未建亦未用： *)
(*   误差账递归取 G_{S m} := 1 + kappa·G_m 后归纳循环依赖清单纯环闭合。     *)
(*   若下游需「闭式 (1-kappa^t)/eta」形，可由本件 igr_gsum 与该     *)
(*                                                              *)
(* 【I4 缺口④核验】UpReqGeomIter.v:869-877 尾注的缺口④（le_b      *)
(*   乘法保序闭包 a <=_B b /\ 0 <=_B c ⟹ a·c <=_B b·c）本件未建：   *)
(*   其右因子非严格情形需 KL_0 精确非负（real_le 形 Gibbs），库内  *)
(*   仅有 eps 形（real_gibbs_inequality_eps），按分层保底纪律不     *)
(*   强造，维持原登记。本件交付的锐利几何和账不经过该缺口。        *)
(*                                                              *)
(* 【R3 见证器账】igr_iter_geom_rate_witness 为 Defined 项级 match t   *)
(*   分派（destruct 不可用于 Defined 项级）；S 支按坑⑨拆为             *)
(*   igr_iter_budget_witness_S 单目标引理 + igr_ring_scale_inv 环件。   *)
(*   见证器口径为锐利账 G_t·eps（非简化账 t·eps）；第四层 _one 为        *)
(*   预算 d:=1 实形（提取面终品）。k-计算器 igr_k_select 的最小 t        *)
(*   搜索取 Q 证书面可判定化（Real 层 Or 编码构造性不可判定）；          *)
(*                                                              *)
(* Assumptions 逐件见文末。                                       *)
(* ============================================================ *)

Print Assumptions igr_geom_step_eps.
Print Assumptions igr_geom_step_discharged_B.
Print Assumptions igr_iter_geom_rate_tight_eps.
Print Assumptions igr_iter_geom_rate_tight.
Print Assumptions igr_iter_geom_rate_eps.
Print Assumptions igr_iter_geom_rate.
Print Assumptions igr_le_b_mult_l.
Print Assumptions igr_powb_le_one.
Print Assumptions igr_ring_scale_inv.
Print Assumptions igr_iter_budget_witness_S.
Print Assumptions igr_iter_geom_rate_witness.
Print Assumptions igr_iter_geom_rate_witness_one.
Print Assumptions igr_k_select_min.
