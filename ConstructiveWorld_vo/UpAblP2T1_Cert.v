(* ==========================================================================)
   UpAblP2T1_Cert.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：kv_id_transport、kv_Z_keep、kv_ofnat_nonneg、kv_ofnat_S_pos、kv_N_pos、kv_single_le_sum、kv_Z_keep_pos、kv_N_R、kv_N_R_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
From Stdlib Require Import Extraction.
From Stdlib Require Import List.
Require Import UpAblT13c_G13.
Require Import UpRealLeB.
Require Import UpReqTempDefs.
Require Import UpReqPowMonoBridge.

(* ================= §1 kv_id_transport 族 ================= *)
Section UpKVDrift.

(* ---------- 0. 契约世界（逐字对齐主会话契约；keep_nonempty 占位解析为
   InT s states + Id (keep s) true，Set 层形态） ---------- *)

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states (@nil Tok)).
Variable K : Tok -> Tok -> Real.
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* Id 沿形传输（bool 投影用；规避 std eq/Prop） *)
Lemma kv_id_transport : forall (A : Set) (x y : A) (P : A -> Set),
  P x -> Id x y -> P y.
Proof.
  intros A x y P p H. exact (match H with id_refl => p end).
Qed.

Definition kv_Z_keep (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.

(* 非空有限表势的正性（states_ne 直用；kv_ofnat 族的前置件） *)
Lemma kv_ofnat_nonneg : forall k : nat, real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - cbn [real_of_nat].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (real_of_nat k))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply real_le_from_lt_aux. apply real_lt_zero_one.
      * exact IH.
Qed.

Lemma kv_ofnat_S_pos : forall k : nat,
  real_lt real_zero (real_of_nat (Datatypes.S k)).
Proof.
  intro k. cbn [real_of_nat].
  apply (real_lt_le_trans real_zero real_one
           (real_plus real_one (real_of_nat k)) real_lt_zero_one).
  apply real_le_plus_nonneg_r_aux.
  apply kv_ofnat_nonneg.
Qed.

Lemma kv_N_pos : real_lt real_zero (real_of_nat (length states)).
Proof.
  revert states_ne.
  induction states as [| x rest IH]; intro Hne.
  - exact (match Hne (@id_refl _ (@nil Tok)) with end).
  - cbn [length].
    exact (kv_ofnat_S_pos (length rest)).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进入提取闭包，   *)
(* 保证 G3 提取 Obj.magic = 0；根内 single_le_sum_aux 的空 match    *)
(* 会产出 2 处 Obj.magic，故不复用；构造对齐成果存档 ）。  *)
Lemma kv_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

(* kv_Z_keep 正性——升级为定理（对齐 ：keep 见证项 K(s,s0) > 0
   且 ≤ kv_Z_keep s；原契约的 Z_keep_pos 前提由此免除） *)
Theorem kv_Z_keep_pos : forall s : Tok, real_lt real_zero (kv_Z_keep s).
Proof.
  intro s.
  destruct keep_nonempty as [s0 [Hk0 Hin0]].
  assert (Hlt0 : real_lt real_zero (if keep s0 then K s s0 else real_zero)).
  { apply (kv_id_transport bool true (keep s0)
             (fun b : bool => real_lt real_zero (if b then K s s0 else real_zero))).
    - apply Kpos.
    - exact (id_sym Hk0). }
  assert (Hle : real_le (if keep s0 then K s s0 else real_zero) (kv_Z_keep s)).
  { apply (kv_single_le_sum Tok
             (fun y : Tok => if keep y then K s y else real_zero)
             s0 states Hin0).
    intro y. destruct (keep y).
    - apply real_le_from_lt_aux. apply Kpos.
    - apply real_le_refl. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if keep s0 then K s s0 else real_zero) (kv_Z_keep s) Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if keep s0 then K s s0 else real_zero) (kv_Z_keep s) Hlt0 Heq).
Qed.

(* 均匀分布与 δ minorization 前提（对齐  结果契约：delta_minor
   对裸 K 逐点，不可省——数学修正警报已吸收）。件 3/4 的语句不依存
   minorization，本块按 Coq 段规则仅在各自使用处进入语句。 *)
Definition kv_N_R : Real := real_of_nat (length states).
Theorem kv_N_R_pos : real_lt real_zero kv_N_R.
Proof.
  unfold kv_N_R.
  revert states_ne.
  induction states as [| x rest IH]; intro Hne.
  - exact (match Hne (@id_refl _ (@nil Tok)) with end).
  - cbn [length].
    exact (kv_ofnat_S_pos (length rest)).
Qed.
Definition kv_U (s' : Tok) : Real := real_inv_pos kv_N_R kv_N_R_pos.

Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (kv_U s')) (K s s').

Definition kv_K_ev (s s' : Tok) : Real :=
  if keep s' then real_mult (K s s') (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)) else real_zero.

(* ---------- 1. 派生定义 ---------- *)

Definition invZK (s : Tok) : Real := real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s).

(* 逐出行误差（drop 质量）与行 TV *)
Definition tail_row (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then real_zero else K s s') states.
Definition tv_row (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => real_abs (real_minus_r (K s s') (kv_K_ev s s'))) states.

(* 一致行误差常数（件 4 前提，规避 sup） *)
Variable c : Real.
Variable Hrow : forall s : Tok, real_le (tv_row s) c.

(* 马尔可夫步算子与双核迭代 *)
Definition lstep (P : Tok -> Tok -> Real) (mu : Tok -> Real) (s' : Tok) : Real :=
  real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states.

Fixpoint kev_iter (n : nat) (mu : Tok -> Real) : Tok -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => lstep kv_K_ev (kev_iter m mu)
  end.

Fixpoint k_iter (n : nat) (mu : Tok -> Real) : Tok -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => lstep K (k_iter m mu)
  end.

Definition Ddist (mu nu : Tok -> Real) : Real :=
  real_list_sum Tok (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states.

(* ---------- 2. 局部代数辅助 ---------- *)

(* 0 + a == a（根内 real_plus_zero 只给 a + 0 == a） *)
Lemma kv_plus_zero_l : forall a : Real, real_eq (real_plus real_zero a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_plus real_zero a) (real_plus a real_zero) a
           (real_plus_comm real_zero a) (real_plus_zero a)).
Qed.

(* 1·a == a（real 层 real_mult_one 为右形 a·1 == a 的左形桥） *)
Lemma kv_one_mult_l : forall a : Real, real_eq (real_mult real_one a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_mult real_one a) (real_mult a real_one) a
           (real_mult_comm real_one a) (real_mult_one a)).
Qed.

(* a·(−b) == −(a·b)（real_opp_mult 的 SYM 快捷形） *)
Lemma kv_opp_mult_bridge : forall a b : Real,
  real_eq (real_mult a (real_opp b)) (real_opp (real_mult a b)).
Proof.
  intros a b. exact (real_eq_sym (real_opp (real_mult a b)) (real_mult a (real_opp b)) (real_opp_mult a b)).
Qed.

(* 2 = 1 + 1 > 0 *)
Lemma kv_two_R_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat; exact real_lt_zero_one.
Qed.

(* 3 = 2 + 1 > 0 *)
Lemma kv_three_R_pos : real_lt real_zero
  (real_plus (real_plus real_one real_one) real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus (real_plus real_one real_one) real_one)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat.
    + exact kv_two_R_pos.
    + exact real_lt_zero_one.
Qed.

(* 右分配：(a + b)·c == a·c + b·c（real_distrib 为左形；comm 桥） *)
Lemma kv_distrib_r : forall a b c0 : Real,
  real_eq (real_mult (real_plus a b) c0)
          (real_plus (real_mult a c0) (real_mult b c0)).
Proof.
  intros a b c0.
  apply (real_eq_trans (real_mult (real_plus a b) c0)
                       (real_mult c0 (real_plus a b)) _).
  - apply real_mult_comm.
  - apply (real_eq_trans (real_mult c0 (real_plus a b))
             (real_plus (real_mult c0 a) (real_mult c0 b)) _).
    + exact (real_distrib c0 a b).
    + apply (RealSetoid.real_eq_plus_compat (real_mult c0 a) (real_mult c0 b)
               (real_mult a c0) (real_mult b c0)
               (real_mult_comm c0 a) (real_mult_comm c0 b)).
Qed.

(* 0 ≤ a ⟹ |a| == a（real_abs_pos_req（lt 版）+ real_abs_zero_req 分解 le） *)
Lemma kv_abs_nonneg_id : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) (real_abs real_zero) a
             (real_abs_eq_compat a real_zero (real_eq_sym real_zero a Heq))
             (real_eq_trans (real_abs real_zero) real_zero a
                real_abs_zero_req Heq)).
Qed.

(* Σ (fun _ => 0) == 0 *)
Lemma kv_sum_zero_list : forall (X : Set) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l. induction l as [| w rest IH].
  - apply real_eq_refl.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_plus real_zero (real_list_sum X (fun _ : X => real_zero) rest))
             (real_plus real_zero real_zero) real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero
               (real_list_sum X (fun _ : X => real_zero) rest)
               real_zero real_zero
               (real_eq_refl real_zero) IH).
    + exact (real_eq_trans (real_plus real_zero real_zero) real_zero real_zero
               (real_eq_refl (real_plus real_zero real_zero))
               (real_plus_zero real_zero)).
Qed.

(* Σ (fun _ => t) == of_nat(|l|)·t（常数和） *)
Lemma kv_sum_const_list : forall (X : Set) (t : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => t) l)
          (real_mult (real_of_nat (length l)) t).
Proof.
  intros X t l. induction l as [| w rest IH].
  - apply (real_eq_sym (real_mult real_zero t) real_zero).
    exact (real_eq_trans (real_mult real_zero t) (real_mult t real_zero) real_zero
             (real_mult_comm real_zero t) (real_mult_zero t)).
  - cbn [real_list_sum length].
    apply (real_eq_trans (real_plus t (real_list_sum X (fun _ : X => t) rest))
             (real_plus (real_mult real_one t)
                        (real_mult (real_of_nat (length rest)) t)) _).
    + apply (RealSetoid.real_eq_plus_compat t
               (real_list_sum X (fun _ : X => t) rest)
               (real_mult real_one t)
               (real_mult (real_of_nat (length rest)) t)
               (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))
               IH).
    + apply real_eq_sym. apply kv_distrib_r.
Qed.

(* t·(inv t·x) == x（inv 吸收通用形；N-平均与 ε/3 分摊共用） *)
Lemma kv_inv_absorb : forall (t : Real) (Ht : real_lt real_zero t) (x : Real),
  real_eq (real_mult t (real_mult (real_inv_pos t Ht) x)) x.
Proof.
  intros t Ht x.
  apply (real_eq_trans (real_mult t (real_mult (real_inv_pos t Ht) x))
                       (real_mult (real_mult t (real_inv_pos t Ht)) x) x).
  - apply real_mult_assoc.
  - apply (real_eq_trans
             (real_mult (real_mult t (real_inv_pos t Ht)) x)
             (real_mult real_one x) x).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult t (real_inv_pos t Ht)) x real_one x).
      * exact (real_inv_pos_correct t Ht).
      * apply real_eq_refl.
    + apply kv_one_mult_l.
Qed.

(* t + t == (1+1)·t *)
Lemma kv_plus_self_two : forall t : Real,
  real_eq (real_plus t t) (real_mult (real_plus real_one real_one) t).
Proof.
  intro t.
  apply (real_eq_trans
           (real_plus t t)
           (real_plus (real_mult t real_one) (real_mult t real_one))
           (real_mult (real_plus real_one real_one) t)).
  - apply (RealSetoid.real_eq_plus_compat t t (real_mult t real_one)
             (real_mult t real_one)
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))).
  - apply (real_eq_trans
             (real_plus (real_mult t real_one) (real_mult t real_one))
             (real_plus (real_mult real_one t) (real_mult real_one t))
             (real_mult (real_plus real_one real_one) t)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult t real_one)
               (real_mult t real_one) (real_mult real_one t) (real_mult real_one t)
               (real_mult_comm t real_one) (real_mult_comm t real_one)).
    + exact (real_eq_sym _ _ (kv_distrib_r real_one real_one t)).
Qed.

(* (t + t) + t == (2+1)·t *)
Lemma kv_plus_self_three : forall t : Real,
  real_eq (real_plus (real_plus t t) t)
          (real_mult (real_plus (real_plus real_one real_one) real_one) t).
Proof.
  intro t.
  apply (real_eq_trans
           (real_plus (real_plus t t) t)
           (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
                      (real_mult real_one t))
           (real_mult (real_plus (real_plus real_one real_one) real_one) t)).
  - apply (RealSetoid.real_eq_plus_compat (real_plus t t) t
             (real_plus (real_mult real_one t) (real_mult real_one t))
             (real_mult real_one t)
             (RealSetoid.real_eq_plus_compat t t (real_mult real_one t)
                (real_mult real_one t)
                (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))
                (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t)))
             (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))).
  - exact (real_eq_sym _ _
             (real_eq_trans
                (real_mult (real_plus (real_plus real_one real_one) real_one) t)
                (real_plus (real_mult (real_plus real_one real_one) t)
                           (real_mult real_one t))
                (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
                           (real_mult real_one t))
                (kv_distrib_r (real_plus real_one real_one) real_one t)
                (RealSetoid.real_eq_plus_compat
                   (real_mult (real_plus real_one real_one) t)
                   (real_mult real_one t)
                   (real_plus (real_mult real_one t) (real_mult real_one t))
                   (real_mult real_one t)
                   (kv_distrib_r real_one real_one t)
                   (real_eq_refl (real_mult real_one t))))).
Qed.


(* |Σ l f| ≤ Σ l |f| + eps（Bishop 逐 eps 形；exact 三角在 Real 层不可得，
   见文件头诚实边界。归纳步 ε 对半，half + half == eps 由 inv2 吸收。） *)
(* 加法重排：(a+(b+h))+h == (a+b)+(h+h)（ε/2 吸收的结构步） *)
Lemma kv_merge_regroup : forall a b h : Real,
  real_eq (real_plus (real_plus a (real_plus b h)) h)
          (real_plus (real_plus a b) (real_plus h h)).
Proof.
  intros a b h.
  apply (real_eq_trans
           (real_plus (real_plus a (real_plus b h)) h)
           (real_plus (real_plus (real_plus a b) h) h)
           (real_plus (real_plus a b) (real_plus h h))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_plus a (real_plus b h)) h
             (real_plus (real_plus a b) h) h
             (real_plus_assoc a b h) (real_eq_refl h)).
  - apply (real_eq_sym _ _ (real_plus_assoc (real_plus a b) h h)).
Qed.

Lemma kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real) (l : list X)
  (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l. induction l as [| w rest IH]; intros eps Heps.
  - apply (real_le_trans
             (real_abs (real_list_sum X f (@nil X))) real_zero
             (real_plus real_zero eps)).
    + apply RealSetoid.real_eq_le. exact real_abs_zero_req.
    + apply real_le_from_lt_aux.
      apply (RealSetoid.real_lt_id_r real_zero eps (real_plus real_zero eps)
               (real_eq_sym _ _ (kv_plus_zero_l eps)) Heps).
  - cbn [real_list_sum].
    assert (Hhalf : real_lt real_zero
              (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                         eps)).
    { apply real_mult_pos_compat.
      - apply real_inv_pos_pos.
      - exact Heps. }
    assert (Hinv2one : real_eq
              (real_plus (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                         (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
              real_one).
    { apply (real_eq_trans
               (real_plus (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
               (real_mult (real_plus real_one real_one)
                          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))).
      - apply kv_plus_self_two.
      - apply real_inv_pos_correct. }
    assert (Hhh : real_eq
              (real_plus (real_mult (real_inv_pos (real_plus real_one real_one)
                                       kv_two_R_pos) eps)
                         (real_mult (real_inv_pos (real_plus real_one real_one)
                                      kv_two_R_pos) eps))
              eps).
    { apply (real_eq_trans
               (real_plus (real_mult (real_inv_pos (real_plus real_one real_one)
                                        kv_two_R_pos) eps)
                          (real_mult (real_inv_pos (real_plus real_one real_one)
                                       kv_two_R_pos) eps))
               (real_mult
                  (real_plus (real_inv_pos (real_plus real_one real_one)
                               kv_two_R_pos)
                     (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
                  eps)
               eps).
      - apply real_eq_sym. apply kv_distrib_r.
      - apply (real_eq_trans _ _ _
                 (RealSetoid.real_eq_mult_compat
                    (real_plus (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos)
                       (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
                    eps real_one eps Hinv2one (real_eq_refl eps))
                 (kv_one_mult_l eps)). }
    assert (H1 : real_le
              (real_abs (real_plus (f w) (real_list_sum X f rest)))
              (real_plus (real_plus (real_abs (f w))
                          (real_abs (real_list_sum X f rest)))
                     (real_mult (real_inv_pos (real_plus real_one real_one)
                                  kv_two_R_pos) eps))).
    { exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest)
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)
               Hhalf). }
    assert (H2 : real_le
              (real_plus (real_plus (real_abs (f w))
                          (real_abs (real_list_sum X f rest)))
                     (real_mult (real_inv_pos (real_plus real_one real_one)
                                  kv_two_R_pos) eps))
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_plus
                       (real_list_sum X (fun x : X => real_abs (f x)) rest)
                       (real_mult (real_inv_pos (real_plus real_one real_one)
                                    kv_two_R_pos) eps)))
                 (real_mult (real_inv_pos (real_plus real_one real_one)
                              kv_two_R_pos) eps))).
    { apply (real_le_plus_compat
               (real_plus (real_abs (f w)) (real_abs (real_list_sum X f rest)))
               (real_plus (real_abs (f w))
                  (real_plus
                     (real_list_sum X (fun x : X => real_abs (f x)) rest)
                     (real_mult (real_inv_pos (real_plus real_one real_one)
                                  kv_two_R_pos) eps)))
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)).
      - apply real_le_plus_compat.
        ++ apply real_le_refl.
        ++ apply IH. exact Hhalf.
      - apply real_le_refl. }
    assert (H3 : real_eq
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_plus
                       (real_list_sum X (fun x : X => real_abs (f x)) rest)
                       (real_mult (real_inv_pos (real_plus real_one real_one)
                                    kv_two_R_pos) eps)))
                 (real_mult (real_inv_pos (real_plus real_one real_one)
                              kv_two_R_pos) eps))
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_list_sum X (fun x : X => real_abs (f x)) rest))
                 (real_plus
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)))).
    { exact (kv_merge_regroup (real_abs (f w))
               (real_list_sum X (fun x : X => real_abs (f x)) rest)
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)). }
    assert (H4 : real_le
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_list_sum X (fun x : X => real_abs (f x)) rest))
                 (real_plus
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)))
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_list_sum X (fun x : X => real_abs (f x)) rest))
                 eps)).
    { apply (RealSetoid.real_eq_le _ _
               (RealSetoid.real_eq_plus_compat _ _ _ _
                  (real_eq_refl _) Hhh)). }
    apply (real_le_trans _ _ _ H1).
    apply (real_le_trans _ _ _ H2).
    apply (real_le_trans _ _ _ (RealSetoid.real_eq_le _ _ H3)).
    exact H4.
Qed.
(* 二重列表和换序：Σ_{y∈l2} Σ_{x∈l1} F x y == Σ_{x∈l1} Σ_{y∈l2} F x y *)
Lemma kv_swap_list : forall (X : Set) (F : X -> X -> Real) (l1 l2 : list X),
  real_eq (real_list_sum X (fun y : X => real_list_sum X (fun x : X => F x y) l1) l2)
          (real_list_sum X (fun x : X => real_list_sum X (fun y : X => F x y) l2) l1).
Proof.
  intros X F l1. induction l1 as [| x l1' IH]; intro l2.
  - cbn [real_list_sum]. apply kv_sum_zero_list.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_list_sum X
                (fun y : X => real_plus (F x y)
                           (real_list_sum X (fun x0 : X => F x0 y) l1')) l2)
             (real_plus (real_list_sum X (fun y : X => F x y) l2)
                (real_list_sum X
                   (fun y : X => real_list_sum X (fun x0 : X => F x0 y) l1') l2))
             _).
    + apply real_list_sum_add.
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum X (fun y : X => F x y) l2)
               (real_list_sum X (fun y : X => real_list_sum X (fun x0 : X => F x0 y) l1') l2)
               (real_list_sum X (fun y : X => F x y) l2)
               (real_list_sum X (fun x0 : X => real_list_sum X (fun y : X => F x0 y) l2) l1')
               (real_eq_refl (real_list_sum X (fun y : X => F x y) l2))
               (IH l2)).
Qed.

Lemma kv_share_pos : forall eps : Real,
  real_lt real_zero eps ->
  real_lt real_zero
    (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps).
Proof.
  intros eps Heps. apply real_mult_pos_compat.
  - apply real_inv_pos_pos.
  - exact Heps.
Qed.

(* ---------- 3. tvL（inv2·Σ|−| 同构形态；依赖 kv_two_R_pos，后置定义） ---- *)

Definition tvL (mu nu : Tok -> Real) : Real :=
  real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) (Ddist mu nu).

(* ---------- 4. 世界层：kv_Z_keep / tail_row / invZK 代数 ---------- *)

(* kv_Z_keep + tail_row == 1（keep 支 + drop 支 == 全行 == 1） *)
Lemma kv_ZK_plus_tail : forall s : Tok,
  real_eq (real_plus (kv_Z_keep s) (tail_row s)) real_one.
Proof.
  intro s.
  apply (real_eq_trans
           (real_plus (kv_Z_keep s) (tail_row s))
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus (if keep s' then K s s' else real_zero)
                           (if keep s' then real_zero else K s s')) states)
           real_one).
  - apply (real_eq_trans
             (real_plus (kv_Z_keep s) (tail_row s))
             (real_plus
                (real_list_sum Tok
                   (fun s' : Tok => if keep s' then K s s' else real_zero) states)
                (real_list_sum Tok
                   (fun s' : Tok => if keep s' then real_zero else K s s') states))
             _).
    + apply real_eq_refl.
    + apply real_eq_sym. apply real_list_sum_add.
  - apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus (if keep s' then K s s' else real_zero)
                             (if keep s' then real_zero else K s s')) states)
             (real_list_sum Tok (fun s' : Tok => K s s') states)
             real_one).
    + apply real_list_sum_ext. intro w. destruct (keep w).
      * apply real_plus_zero.
      * apply kv_plus_zero_l.
    + exact (Krow s).
Qed.
(* tail_row == 1 − kv_Z_keep（由 Z + tail == 1 换形） *)
Lemma kv_tail_one_minus : forall s : Tok,
  real_eq (tail_row s) (real_minus_r real_one (kv_Z_keep s)).
Proof.
  intro s.
  assert (Hzt : real_eq (real_plus (kv_Z_keep s) (tail_row s)) real_one)
    by exact (kv_ZK_plus_tail s).
  apply real_eq_sym.
  apply (real_eq_trans (real_minus_r real_one (kv_Z_keep s))
           (real_minus_r (real_plus (kv_Z_keep s) (tail_row s)) (kv_Z_keep s))
           (tail_row s)).
  - unfold real_minus_r.
    apply (real_eq_trans
             (real_plus real_one (real_opp (kv_Z_keep s)))
             (real_plus (real_plus (kv_Z_keep s) (tail_row s)) (real_opp (kv_Z_keep s)))
             _).
    + apply (RealSetoid.real_eq_plus_compat real_one (real_opp (kv_Z_keep s))
               (real_plus (kv_Z_keep s) (tail_row s)) (real_opp (kv_Z_keep s))
               (real_eq_sym (real_plus (kv_Z_keep s) (tail_row s)) real_one Hzt)
               (real_eq_refl _)).
    + apply real_eq_refl.
  - unfold real_minus_r.
    assert (Hs1 : real_eq
               (real_plus (real_plus (kv_Z_keep s) (tail_row s)) (real_opp (kv_Z_keep s)))
               (real_plus (kv_Z_keep s) (real_plus (tail_row s) (real_opp (kv_Z_keep s))))).
    { apply real_eq_sym. apply real_plus_assoc. }
    assert (Hs2 : real_eq
               (real_plus (kv_Z_keep s) (real_plus (tail_row s) (real_opp (kv_Z_keep s))))
               (real_plus (kv_Z_keep s) (real_plus (real_opp (kv_Z_keep s)) (tail_row s)))).
    { apply (RealSetoid.real_eq_plus_compat _ _ _ _
               (real_eq_refl _) (real_plus_comm _ _)). }
    assert (Hs3 : real_eq
               (real_plus (kv_Z_keep s) (real_plus (real_opp (kv_Z_keep s)) (tail_row s)))
               (real_plus (real_plus (kv_Z_keep s) (real_opp (kv_Z_keep s))) (tail_row s))).
    { apply real_plus_assoc. }
    assert (Hs4 : real_eq
               (real_plus (real_plus (kv_Z_keep s) (real_opp (kv_Z_keep s))) (tail_row s))
               (real_plus real_zero (tail_row s))).
    { apply (RealSetoid.real_eq_plus_compat
               (real_plus (kv_Z_keep s) (real_opp (kv_Z_keep s))) (tail_row s)
               real_zero (tail_row s)
               (real_plus_opp (kv_Z_keep s)) (real_eq_refl _)). }
    apply (real_eq_trans _ _ _ Hs1
             (real_eq_trans _ _ _ Hs2
                (real_eq_trans _ _ _ Hs3
                   (real_eq_trans _ _ _ Hs4 (kv_plus_zero_l _))))).
Qed.
(* 逐点符号证书恒等式（和式 RHS）：
   |K − kv_K_ev| == (if keep then kv_K_ev − K else 0) + (if keep then 0 else K)
   keep 支用 real_abs_minus_r_nonneg_aux（K ≤ kv_K_ev 符号证书），drop 支 |K−0| == K *)

Lemma kv_ZK_le_one : forall s : Tok, real_le (kv_Z_keep s) real_one.
Proof.
  intro s.
  apply (real_le_trans (kv_Z_keep s)
           (real_list_sum Tok (fun s' : Tok => K s s') states) real_one).
  - unfold kv_Z_keep. apply real_list_sum_le. intro w. destruct (keep w).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply Kpos.
  - apply RealSetoid.real_eq_le. exact (Krow s).
Qed.

(* invZK ≥ 1（Z ≤ 1 + inv 反序 + inv(1) == 1） *)
Lemma kv_invZ_ge_one : forall s : Tok, real_le real_one (invZK s).
Proof.
  intro s.
  apply (RealSetoid.real_le_id_l real_one
           (real_inv_pos real_one real_lt_zero_one) (invZK s)).
  - apply (real_eq_sym _ _
             (real_eq_trans (real_inv_pos real_one real_lt_zero_one)
                (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
                real_one
                (real_eq_sym _ _ (kv_one_mult_l
                   (real_inv_pos real_one real_lt_zero_one)))
                (real_inv_pos_correct real_one real_lt_zero_one))).
  - exact (real_inv_pos_le_compat (kv_Z_keep s) real_one
             (kv_Z_keep_pos s) real_lt_zero_one (kv_ZK_le_one s)).
Qed.

(* keep 支符号证书（缩放形）：K ≤ K·invZ（1 ≤ invZ 左乘保序） *)
Lemma kv_K_le_Kev_scaled : forall s s' : Tok,
  real_le (K s s') (real_mult (K s s') (invZK s)).
Proof.
  intros s s'.
  apply (real_le_trans _ (real_mult (K s s') real_one) _).
  - apply RealSetoid.real_eq_le. apply real_eq_sym. apply real_mult_one.
  - exact (real_le_mult_compat_l_aux real_one (invZK s) (K s s')
             (Kpos s s') (kv_invZ_ge_one s)).
Qed.

(* ext 逐点：kv_K_ev 求和项 == (if keep then K else 0)·invZ（行归一化用） *)
Lemma kv_summand_eq : forall (s w : Tok),
  real_eq
    (if keep w
     then real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))
     else real_zero)
    (real_mult (if keep w then K s w else real_zero)
               (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))).
Proof.
  intros s w. destruct (keep w).
  - apply real_eq_refl.
  - apply (real_eq_sym (real_mult real_zero
                          (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))) real_zero
             (real_eq_trans
                (real_mult real_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                (real_mult (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)) real_zero)
                real_zero
                (real_mult_comm real_zero
                   (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                (real_mult_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))))).
Qed.

(* 乘法形逐点：(if keep then kv_K_ev−K else 0) == (if keep then K else 0)·(invZ−1) *)
Lemma kv_summand_scaled : forall (s w : Tok),
  real_eq
    (if keep w then real_minus_r (kv_K_ev s w) (K s w) else real_zero)
    (real_mult (if keep w then K s w else real_zero)
               (real_minus_r (invZK s) real_one)).
Proof.
  intros s w. unfold kv_K_ev. destruct (keep w).
  - (* keep 支：(K·invZ) + (−K) == K·(invZ + (−1))，经 −K == K·(−1) 桥 + sym 分配 *)
    apply (real_eq_trans
             (real_minus_r
                (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                (K s w))
             (real_plus
                (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                (real_opp (K s w)))
             (real_mult (K s w) (real_minus_r (invZK s) real_one))).
    + apply real_eq_refl.
    + apply (real_eq_trans
                (real_plus
                   (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                   (real_opp (K s w)))
                (real_plus
                   (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                   (real_mult (K s w) (real_opp real_one)))
                (real_mult (K s w) (real_minus_r (invZK s) real_one))).
      * apply (RealSetoid.real_eq_plus_compat
                  (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                  (real_opp (K s w))
                  (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                  (real_mult (K s w) (real_opp real_one))
                  (real_eq_refl _)
                  (real_eq_trans (real_opp (K s w))
                     (real_opp (real_mult (K s w) real_one))
                     (real_mult (K s w) (real_opp real_one))
                     (RealSetoid.real_eq_opp_compat (K s w)
                        (real_mult (K s w) real_one)
                        (real_eq_sym (real_mult (K s w) real_one) (K s w)
                           (real_mult_one (K s w))))
                     (real_opp_mult (K s w) real_one))).
      * apply real_eq_sym.
        exact (real_distrib (K s w)
                 (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)) (real_opp real_one)).
  - (* drop 支：0 == 0·(invZ−1)（real_eq_sym 假设位：conclusion real_eq y x） *)
    apply (real_eq_sym (real_mult real_zero (real_minus_r (invZK s) real_one))
              real_zero
              (real_eq_trans
                 (real_mult real_zero (real_minus_r (invZK s) real_one))
                 (real_mult (real_minus_r (invZK s) real_one) real_zero)
                 real_zero
                 (real_mult_comm real_zero (real_minus_r (invZK s) real_one))
                 (real_mult_zero (real_minus_r (invZK s) real_one)))).
Qed.

(* 件 1 副本：kv_K_ev 行归一化 Σ_{s'} kv_K_ev(s,s') == 1
   （依 _kv_tail.txt 快照还原；变动归纳的归一化前提所需） *)
Lemma kv_kev_row_one : forall s : Tok,
  real_eq (real_list_sum Tok (kv_K_ev s) states) real_one.
Proof.
  intro s. unfold kv_K_ev.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun w : Tok =>
                 (if keep w
                  then real_mult (K s w)
                       (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))
                  else real_zero)) states)
           (real_mult (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)) (kv_Z_keep s))
           real_one).
  - apply (real_eq_trans _ _ _
             (real_list_sum_ext Tok
                (fun w : Tok =>
                   (if keep w
                    then real_mult (K s w)
                         (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))
                    else real_zero))
                (fun w : Tok =>
                   real_mult (if keep w then K s w else real_zero)
                             (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))) states
                (kv_summand_eq s))
             (real_list_sum_linear_r Tok
                (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))
                (fun w : Tok => if keep w then K s w else real_zero) states)).
  - apply (real_eq_trans
              (real_mult (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)) (kv_Z_keep s))
              (real_mult (kv_Z_keep s) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
              real_one).
    + apply real_mult_comm.
    + exact (real_inv_pos_correct (kv_Z_keep s) (kv_Z_keep_pos s)).
Qed.

(* keep 支和的缩放：Σ_keep(kv_K_ev − K) == (invZ − 1)·kv_Z_keep
   （快照重写：逐点 kv_summand_scaled + real_list_sum_linear_r 两行闭合） *)
Lemma kv_gsum_scaled : forall s : Tok,
  real_eq
    (real_list_sum Tok
       (fun s' : Tok =>
          if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
       states)
    (real_mult (real_minus_r (invZK s) real_one) (kv_Z_keep s)).
Proof.
  intro s.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
              states)
           (real_list_sum Tok
              (fun w : Tok =>
                 real_mult (if keep w then K s w else real_zero)
                           (real_minus_r (invZK s) real_one))
              states)
           (real_mult (real_minus_r (invZK s) real_one) (kv_Z_keep s))).
  - apply real_list_sum_ext. intro w. apply kv_summand_scaled.
  - apply (real_list_sum_linear_r Tok
              (real_minus_r (invZK s) real_one)
              (fun w : Tok => if keep w then K s w else real_zero) states).
Qed.

(* (invZ − 1)·kv_Z_keep == 1 − kv_Z_keep == tail_row
   （快照重写：kv_distrib_r + inv_pos_correct/opp 桥 compat，尾接 kv_tail_one_minus） *)
Lemma kv_scaledZ_tail : forall s : Tok,
  real_eq (real_mult (real_minus_r (invZK s) real_one) (kv_Z_keep s)) (tail_row s).
Proof.
  intro s.
  apply (real_eq_trans
           (real_mult (real_minus_r (invZK s) real_one) (kv_Z_keep s))
           (real_minus_r real_one (kv_Z_keep s))
           (tail_row s)).
  - apply (real_eq_trans
              (real_mult (real_minus_r (invZK s) real_one) (kv_Z_keep s))
              (real_plus (real_mult (invZK s) (kv_Z_keep s))
                         (real_mult (real_opp real_one) (kv_Z_keep s)))
              (real_minus_r real_one (kv_Z_keep s))).
    + apply (kv_distrib_r (invZK s) (real_opp real_one) (kv_Z_keep s)).
    + apply (RealSetoid.real_eq_plus_compat
               (real_mult (invZK s) (kv_Z_keep s))
               (real_mult (real_opp real_one) (kv_Z_keep s))
               real_one (real_opp (kv_Z_keep s))
               (real_eq_trans (real_mult (invZK s) (kv_Z_keep s))
                  (real_mult (kv_Z_keep s) (invZK s)) real_one
                  (real_mult_comm (invZK s) (kv_Z_keep s))
                  (real_inv_pos_correct (kv_Z_keep s) (kv_Z_keep_pos s)))
               (real_eq_trans (real_mult (real_opp real_one) (kv_Z_keep s))
                  (real_opp (real_mult real_one (kv_Z_keep s)))
                  (real_opp (kv_Z_keep s))
                  (real_eq_sym _ _ (real_opp_mult_r real_one (kv_Z_keep s)))
                  (RealSetoid.real_eq_opp_compat (real_mult real_one (kv_Z_keep s))
                     (kv_Z_keep s) (kv_one_mult_l (kv_Z_keep s))))).
  - exact (real_eq_sym _ _ (kv_tail_one_minus s)).
Qed.

(* 逐点符号证书：|K − kv_K_ev| == keep ? (kv_K_ev − K) : K
   （keep 支 real_abs_minus_r_nonneg_aux；drop 支 −0/加零/|K|=K 桥） *)
Lemma kv_tvrow_pointwise : forall s w : Tok,
  real_eq (real_abs (real_minus_r (K s w) (kv_K_ev s w)))
          (if keep w then real_minus_r (kv_K_ev s w) (K s w) else K s w).
Proof.
  intros s w. unfold kv_K_ev. destruct (keep w).
  - exact (real_abs_minus_r_nonneg_aux (K s w)
             (real_mult (K s w) (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
             (kv_K_le_Kev_scaled s w)).
  - apply (real_eq_trans
             (real_abs (real_plus (K s w) (real_opp real_zero)))
             (real_abs (K s w)) (K s w)).
    + apply real_abs_eq_compat.
      apply (real_eq_trans
               (real_plus (K s w) (real_opp real_zero))
               (real_plus (K s w) real_zero) (K s w)).
      * apply (RealSetoid.real_eq_plus_compat (K s w) (real_opp real_zero)
                 (K s w) real_zero (real_eq_refl _) real_opp_zero).
      * apply real_plus_zero.
    + exact (kv_abs_nonneg_id (K s w)
               (real_le_from_lt_aux real_zero (K s w) (Kpos s w))).
Qed.

(* 分部：tv_row == Σ_keep(kv_K_ev−K) + Σ_drop K（逐点证书 ext + 逐项拆装 ext/add） *)
Lemma kv_tvrow_split : forall s : Tok,
  real_eq (tv_row s)
          (real_plus
             (real_list_sum Tok
                (fun s' : Tok =>
                   if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
                states)
             (tail_row s)).
Proof.
  intro s. unfold tv_row.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (K s s') (kv_K_ev s s'))) states)
           (real_plus
              (real_list_sum Tok
                 (fun w : Tok =>
                    if keep w then real_minus_r (kv_K_ev s w) (K s w) else real_zero)
                 states)
              (real_list_sum Tok
                 (fun w : Tok => if keep w then real_zero else K s w)
                 states))
           (real_plus
              (real_list_sum Tok
                 (fun s' : Tok =>
                    if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
                 states)
              (tail_row s))).
  - apply (real_eq_trans
              (real_list_sum Tok
                 (fun s' : Tok =>
                    real_abs (real_minus_r (K s s') (kv_K_ev s s'))) states)
              (real_list_sum Tok
                 (fun w : Tok =>
                    if keep w then real_minus_r (kv_K_ev s w) (K s w) else K s w)
                 states)
              (real_plus
                 (real_list_sum Tok
                    (fun w : Tok =>
                       if keep w then real_minus_r (kv_K_ev s w) (K s w) else real_zero)
                    states)
                 (real_list_sum Tok
                    (fun w : Tok => if keep w then real_zero else K s w)
                    states))).
    + apply real_list_sum_ext. exact (kv_tvrow_pointwise s).
    + apply (real_eq_trans
                (real_list_sum Tok
                   (fun w : Tok =>
                      if keep w then real_minus_r (kv_K_ev s w) (K s w) else K s w)
                   states)
                (real_list_sum Tok
                   (fun w : Tok =>
                      real_plus
                        (if keep w then real_minus_r (kv_K_ev s w) (K s w)
                         else real_zero)
                        (if keep w then real_zero else K s w))
                   states)
                (real_plus
                   (real_list_sum Tok
                      (fun w : Tok =>
                         if keep w then real_minus_r (kv_K_ev s w) (K s w)
                         else real_zero)
                      states)
                   (real_list_sum Tok
                      (fun w : Tok => if keep w then real_zero else K s w)
                      states))).
      * apply real_list_sum_ext. intro w. destruct (keep w).
        -- apply real_eq_sym. apply real_plus_zero.
        -- apply real_eq_sym. apply kv_plus_zero_l.
      * apply real_list_sum_add.
  - apply real_eq_refl.
Qed.

(* ===================== 件 3 主结果：精确恒等式 =========================
   tv_row(s) == tail_row(s) + tail_row(s)（== 2·tail_row == 2·(1 − kv_Z_keep)） *)
Theorem kev_row_tv_exact : forall s : Tok,
  real_eq (tv_row s) (real_plus (tail_row s) (tail_row s)).
Proof.
  intro s.
  apply (real_eq_trans (tv_row s)
           (real_plus
              (real_list_sum Tok
                 (fun s' : Tok =>
                    if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
                 states)
              (tail_row s))
           (real_plus (tail_row s) (tail_row s))).
  - exact (kv_tvrow_split s).
  - apply (RealSetoid.real_eq_plus_compat
             (real_list_sum Tok
                (fun s' : Tok =>
                   if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
                states)
             (tail_row s)
             (tail_row s) (tail_row s)
             (real_eq_trans
                (real_list_sum Tok
                   (fun s' : Tok =>
                      if keep s' then real_minus_r (kv_K_ev s s') (K s s') else real_zero)
                   states)
                (real_mult (real_minus_r (invZK s) real_one) (kv_Z_keep s))
                (tail_row s)
                (kv_gsum_scaled s) (kv_scaledZ_tail s))
             (real_eq_refl _)).
Qed.

(* ≤ 2·tail 形（与 exact 并列结果；real_le Type 编码，无 Prop 泄露） *)
Corollary kev_row_tv_bound : forall s : Tok,
  real_le (tv_row s) (real_plus (tail_row s) (tail_row s)).
Proof.
  intro s. apply RealSetoid.real_eq_le. exact (kev_row_tv_exact s).
Qed.

(* 论文形态：tv_row == 2·(1 − kv_Z_keep)（语句依 _kv_tail.txt 快照还原） *)
Corollary kev_row_tv_one_minus_Z : forall s : Tok,
  real_eq (tv_row s)
          (real_mult (real_plus real_one real_one)
                     (real_minus_r real_one (kv_Z_keep s))).
Proof.
  intro s.
  apply (real_eq_trans (tv_row s)
           (real_mult (real_plus real_one real_one) (tail_row s)) _).
  - apply (real_eq_trans (tv_row s) (real_plus (tail_row s) (tail_row s)) _).
    + exact (kev_row_tv_exact s).
    + apply kv_plus_self_two.
  - apply (RealSetoid.real_eq_mult_compat
             (real_plus real_one real_one) (tail_row s)
             (real_plus real_one real_one) (real_minus_r real_one (kv_Z_keep s))
             (real_eq_refl _) (kv_tail_one_minus s)).
Qed.

(* ---------- 件 4 机器：步算子代数 ---------- *)

(* 步差恒等式（同核）：Pμ(s') − Pν(s') == Σ_s (μ−ν)(s)·P(s,s') *)
Lemma kv_lstep_minus_pt2 : forall (P : Tok -> Tok -> Real) (mu nu : Tok -> Real)
  (s' : Tok),
  real_eq (real_minus_r (lstep P mu s') (lstep P nu s'))
          (real_list_sum Tok
             (fun s : Tok => real_mult (real_minus_r (mu s) (nu s)) (P s s')) states).
Proof.
  intros P mu nu s'. unfold lstep, real_minus_r.
  apply (real_eq_trans
           (real_plus
              (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
              (real_opp
                 (real_list_sum Tok (fun s : Tok => real_mult (nu s) (P s s')) states)))
           (real_list_sum Tok
              (fun s : Tok =>
                 real_plus (real_mult (mu s) (P s s'))
                           (real_opp (real_mult (nu s) (P s s')))) states)
           _).
  - apply (real_eq_trans
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
                (real_opp
                   (real_list_sum Tok (fun s : Tok => real_mult (nu s) (P s s')) states)))
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
                (real_list_sum Tok
                   (fun s : Tok => real_opp (real_mult (nu s) (P s s'))) states))
             _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
               (real_opp
                  (real_list_sum Tok (fun s : Tok => real_mult (nu s) (P s s')) states))
               (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
               (real_list_sum Tok
                  (fun s : Tok => real_opp (real_mult (nu s) (P s s'))) states)
               (real_eq_refl _)
               (real_eq_sym _ _
                  (real_list_sum_opp Tok (fun s : Tok => real_mult (nu s) (P s s')) states))).
    + apply real_eq_sym. apply real_list_sum_add.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_plus (real_mult (mu s) (P s s'))
                        (real_opp (real_mult (nu s) (P s s'))))
             (real_plus (real_mult (mu s) (P s s'))
                        (real_mult (real_opp (nu s)) (P s s'))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (mu s) (P s s'))
               (real_opp (real_mult (nu s) (P s s')))
               (real_mult (mu s) (P s s'))
               (real_mult (real_opp (nu s)) (P s s'))
               (real_eq_refl _)
               (real_opp_mult_r (nu s) (P s s'))).
    + apply real_eq_sym. apply kv_distrib_r.
Qed.

(* 两核心步差恒等式（同权重 w）：
   Σ_s w(s)·P(s,s') − Σ_s w(s)·Q(s,s') == Σ_s w(s)·(P−Q)(s,s') *)
Lemma kv_lstep2_minus_pt : forall (P Q : Tok -> Tok -> Real) (w : Tok -> Real)
  (s' : Tok),
  real_eq (real_minus_r (lstep P w s') (lstep Q w s'))
          (real_list_sum Tok
             (fun s : Tok =>
                real_mult (w s) (real_minus_r (P s s') (Q s s'))) states).
Proof.
  intros P Q w s'. unfold lstep, real_minus_r.
  apply (real_eq_trans
           (real_plus
              (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
              (real_opp
                 (real_list_sum Tok (fun s : Tok => real_mult (w s) (Q s s')) states)))
           (real_list_sum Tok
              (fun s : Tok =>
                 real_plus (real_mult (w s) (P s s'))
                           (real_opp (real_mult (w s) (Q s s')))) states)
           _).
  - apply (real_eq_trans
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
                (real_opp
                   (real_list_sum Tok (fun s : Tok => real_mult (w s) (Q s s')) states)))
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
                (real_list_sum Tok
                   (fun s : Tok => real_opp (real_mult (w s) (Q s s'))) states))
             _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
               (real_opp
                  (real_list_sum Tok (fun s : Tok => real_mult (w s) (Q s s')) states))
               (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
               (real_list_sum Tok
                  (fun s : Tok => real_opp (real_mult (w s) (Q s s'))) states)
               (real_eq_refl _)
               (real_eq_sym _ _
                  (real_list_sum_opp Tok (fun s : Tok => real_mult (w s) (Q s s')) states))).
    + apply real_eq_sym. apply real_list_sum_add.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_plus (real_mult (w s) (P s s'))
                        (real_opp (real_mult (w s) (Q s s'))))
             (real_plus (real_mult (w s) (P s s'))
                        (real_mult (w s) (real_opp (Q s s')))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (w s) (P s s'))
               (real_opp (real_mult (w s) (Q s s')))
               (real_mult (w s) (P s s'))
               (real_mult (w s) (real_opp (Q s s')))
               (real_eq_refl _)
               (real_eq_sym _ _ (real_mult_opp_l (w s) (Q s s')))).
    + apply real_eq_sym. apply real_distrib.
Qed.

(* D(μ,μ) == 0 *)
Lemma kv_D_zero : forall mu : Tok -> Real, real_eq (Ddist mu mu) real_zero.
Proof.
  intro mu. unfold Ddist.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun x : Tok => real_abs (real_minus_r (mu x) (mu x))) states)
           (real_list_sum Tok (fun x : Tok => real_zero) states) real_zero).
  - apply real_list_sum_ext. intro x.
    apply (real_eq_trans (real_abs (real_minus_r (mu x) (mu x)))
             (real_abs real_zero) real_zero).
    + apply real_abs_eq_compat. apply real_plus_opp.
    + exact real_abs_zero_req.
  - apply kv_sum_zero_list.
Qed.

(* 马尔可夫步保持质量和 *)
Lemma kv_lstep_norm : forall (P : Tok -> Tok -> Real),
  (forall s : Tok, real_eq (real_list_sum Tok (P s) states) real_one) ->
  forall mu : Tok -> Real,
  real_eq (real_list_sum Tok (fun s' : Tok => lstep P mu s') states)
          (real_list_sum Tok mu states).
Proof.
  intros P HP mu. unfold lstep.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
              states)
           (real_list_sum Tok
              (fun s : Tok =>
                 real_list_sum Tok (fun s' : Tok => real_mult (mu s) (P s s')) states)
              states)
           (real_list_sum Tok mu states)).
  - apply kv_swap_list.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_list_sum Tok (fun s' : Tok => real_mult (mu s) (P s s')) states)
             (real_mult (mu s) (real_list_sum Tok (P s) states)) (mu s)).
    + apply real_list_sum_linear.
    + apply (real_eq_trans
               (real_mult (mu s) (real_list_sum Tok (P s) states))
               (real_mult (mu s) real_one) (mu s)).
      * apply (RealSetoid.real_eq_mult_compat (mu s)
                 (real_list_sum Tok (P s) states) (mu s) real_one
                 (real_eq_refl (mu s)) (HP s)).
      * apply real_mult_one.
Qed.

(* 步算子非负（μ ≥ 0、P ≥ 0） *)
Lemma kv_lstep_nonneg : forall (P : Tok -> Tok -> Real),
  (forall s s' : Tok, real_le real_zero (P s s')) ->
  forall mu : Tok -> Real,
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall s' : Tok, real_le real_zero (lstep P mu s').
Proof.
  intros P HP mu Hmu s'. unfold lstep.
  apply real_list_sum_nonneg. intro s.
  apply (RealSetoid.real_le_id_l real_zero
           (real_mult real_zero (P s s')) (real_mult (mu s) (P s s'))).
  - apply (real_eq_sym (real_mult real_zero (P s s')) real_zero).
    exact (real_eq_trans (real_mult real_zero (P s s'))
             (real_mult (P s s') real_zero) real_zero
             (real_mult_comm real_zero (P s s')) (real_mult_zero (P s s'))).
  - exact (real_le_mult_compat_weak real_zero (mu s) (P s s') (HP s s') (Hmu s)).
Qed.

(* kv_K_ev ≥ 0（契约核的非负性） *)
Lemma kv_K_ev_nonneg : forall s s' : Tok, real_le real_zero (kv_K_ev s s').
Proof.
  intros s s'. unfold kv_K_ev. destruct (keep s').
  - apply (RealSetoid.real_le_id_l real_zero
             (real_mult real_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
             (real_mult (K s s') (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))).
    + apply (real_eq_sym (real_mult real_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
               real_zero).
      exact (real_eq_trans
                (real_mult real_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                (real_mult (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)) real_zero)
                real_zero
                (real_mult_comm real_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
                (real_mult_zero (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s)))).
    + exact (real_le_mult_compat_weak real_zero (K s s')
               (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))
               (real_le_from_lt_aux real_zero
                  (real_inv_pos (kv_Z_keep s) (kv_Z_keep_pos s))
                  (real_inv_pos_pos (kv_Z_keep s) (kv_Z_keep_pos s)))
               (real_le_from_lt_aux real_zero (K s s') (Kpos s s'))).
  - apply real_le_refl.
Qed.

(* 迭代归一化与非负 *)
Lemma kv_kev_iter_norm : forall (n : nat) (mu : Tok -> Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  real_eq (real_list_sum Tok (kev_iter n mu) states) real_one.
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu.
  - exact Hmu.
  - exact (real_eq_trans _ _ _
             (kv_lstep_norm kv_K_ev (fun s : Tok => kv_kev_row_one s) (kev_iter n mu))
             (IH mu Hmu)).
Qed.

Lemma kv_k_iter_norm : forall (n : nat) (mu : Tok -> Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  real_eq (real_list_sum Tok (k_iter n mu) states) real_one.
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu.
  - exact Hmu.
  - exact (real_eq_trans _ _ _
             (kv_lstep_norm K Krow (k_iter n mu))
             (IH mu Hmu)).
Qed.

Lemma kv_kev_iter_nonneg : forall (n : nat) (mu : Tok -> Real),
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall s : Tok, real_le real_zero (kev_iter n mu s).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu s'.
  - exact (Hmu s').
  - exact (kv_lstep_nonneg kv_K_ev kv_K_ev_nonneg (kev_iter n mu) (IH mu Hmu) s').
Qed.

Lemma kv_k_iter_nonneg : forall (n : nat) (mu : Tok -> Real),
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall s : Tok, real_le real_zero (k_iter n mu s).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu s'.
  - exact (Hmu s').
  - exact (kv_lstep_nonneg K
             (fun s s' : Tok => real_le_from_lt_aux real_zero (K s s') (Kpos s s'))
             (k_iter n mu) (IH mu Hmu) s').
Qed.

(* D(μ,ν) 双重和化简：Σ_s'Σ_s |(μ−ν)(s)·P(s,s')| == Σ_s |μ(s)−ν(s)|
   （kv_swap_list 换序 + 逐点 abs-mult 拆积 + 行归一吸收；tactic 模式统一，
   term 模式下 kv_swap_list 结论与目标 alpha 等价却报无法统一） *)
Lemma kv_dsum_abs_eq : forall (P : Tok -> Tok -> Real),
  (forall s s' : Tok, real_le real_zero (P s s')) ->
  (forall s : Tok, real_eq (real_list_sum Tok (P s) states) real_one) ->
  forall mu nu : Tok -> Real,
  real_eq (real_list_sum Tok
             (fun s' : Tok =>
                real_list_sum Tok
                  (fun s : Tok =>
                     real_abs (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                  states)
              states)
          (real_list_sum Tok
             (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states).
Proof.
  intros P Hnn HP mu nu.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                   states)
              states)
           (real_list_sum Tok
              (fun s : Tok =>
                 real_list_sum Tok
                   (fun s' : Tok =>
                      real_abs
                        (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                   states)
              states) _).
  - apply kv_swap_list.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_abs
                     (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                states)
             (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                        (real_list_sum Tok (P s) states)) _).
    + apply (real_eq_trans
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_abs
                       (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                  states)
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_mult (real_abs (real_minus_r (mu s) (nu s)))
                               (P s s'))
                  states) _).
      * apply real_list_sum_ext. intro s'.
        apply (real_eq_trans
                 (real_abs
                    (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                 (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                            (real_abs (P s s')))
                 (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                            (P s s'))).
        -- exact (real_abs_mult_req (real_minus_r (mu s) (nu s)) (P s s')).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_abs (real_minus_r (mu s) (nu s)))
                    (real_abs (P s s'))
                    (real_abs (real_minus_r (mu s) (nu s)))
                    (P s s')
                    (real_eq_refl _)
                    (kv_abs_nonneg_id (P s s') (Hnn s s'))).
      * apply real_list_sum_linear.
    + exact (real_eq_trans _ _ _
               (RealSetoid.real_eq_mult_compat
                  (real_abs (real_minus_r (mu s) (nu s)))
                  (real_list_sum Tok (P s) states)
                  (real_abs (real_minus_r (mu s) (nu s))) real_one
                  (real_eq_refl _) (HP s))
               (real_mult_one (real_abs (real_minus_r (mu s) (nu s))))).
Qed.

(* 马尔可夫核 TV 非扩张（Bishop ε 形）：
   D(Pμ, Pν) ≤ D(μ,ν) + ε——行三角 + 二重和换序 + 行归一吸收 *)
Lemma kv_nonexpansive : forall (P : Tok -> Tok -> Real),
  (forall s : Tok, real_eq (real_list_sum Tok (P s) states) real_one) ->
  (forall s s' : Tok, real_le real_zero (P s s')) ->
  forall mu nu : Tok -> Real, forall eps : Real,
  real_lt real_zero eps ->
  real_le (Ddist (lstep P mu) (lstep P nu)) (real_plus (Ddist mu nu) eps).
Proof.
  intros P HP Hnn mu nu eps Heps.
  assert (Hshare : real_lt real_zero
            (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps))
    by (apply kv_share_pos; exact Heps).
  unfold Ddist.
  apply (real_le_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (lstep P mu s') (lstep P nu s'))) states)
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_abs
                           (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                      states)
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps))
              states)
           (real_plus
              (real_list_sum Tok
                 (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states)
              eps)).
  - apply real_list_sum_le. intro s'.
    apply (real_le_trans
             (real_abs (real_minus_r (lstep P mu s') (lstep P nu s')))
             (real_abs
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (real_minus_r (mu s) (nu s)) (P s s')) states))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (real_minus_r (mu s) (nu s)) (P s s'))) states)
                (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                           eps))).
    + apply inr. apply real_abs_eq_compat. exact (kv_lstep_minus_pt2 P mu nu s').
    + exact (kv_abs_triangle_list_eps Tok
               (fun s : Tok => real_mult (real_minus_r (mu s) (nu s)) (P s s'))
               states _ Hshare).
  - apply inr.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_abs
                             (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                        states)
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                states)
             (real_plus
                (real_list_sum Tok
                   (fun s' : Tok =>
                      real_list_sum Tok
                        (fun s : Tok =>
                           real_abs
                             (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                        states)
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps)))
             (real_plus
                (real_list_sum Tok
                   (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states)
                eps)).
    + apply (real_eq_trans _ _ _
               (real_list_sum_add Tok
                  (fun s : Tok =>
                     real_list_sum Tok
                       (fun s0 : Tok =>
                          real_abs
                            (real_mult (real_minus_r (mu s0) (nu s0)) (P s0 s)))
                       states)
                  (fun _ : Tok =>
                     real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                               eps)
                  states)
               (RealSetoid.real_eq_plus_compat
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_list_sum Tok
                          (fun s0 : Tok =>
                             real_abs
                               (real_mult (real_minus_r (mu s0) (nu s0)) (P s0 s)))
                          states)
                      states)
                  (real_list_sum Tok
                     (fun _ : Tok =>
                        real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                  eps)
                     states)
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_list_sum Tok
                          (fun s0 : Tok =>
                             real_abs
                               (real_mult (real_minus_r (mu s0) (nu s0)) (P s0 s)))
                          states)
                      states)
                  (real_mult (real_of_nat (length states))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                  (real_eq_refl _)
                  (kv_sum_const_list Tok
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps)
                     states))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_list_sum Tok
                       (fun s : Tok =>
                          real_abs
                            (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                       states)
                   states)
               (real_mult (real_of_nat (length states))
                  (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                             eps))
               (real_list_sum Tok
                  (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states)
               eps
               (kv_dsum_abs_eq P Hnn HP mu nu)
               (kv_inv_absorb (real_of_nat (length states)) kv_N_pos eps)).
Qed.

(* a − c == (a − b) + (b − c)（D 三角的逐点恒等式） *)
Lemma kv_minus_split : forall a b c0 : Real,
  real_eq (real_minus_r a c0)
          (real_plus (real_minus_r a b) (real_minus_r b c0)).
Proof.
  intros a b c0. unfold real_minus_r.
  apply real_eq_sym.
  apply (real_eq_trans
           (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c0)))
           (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c0))))
           (real_plus a (real_opp c0))).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (RealSetoid.real_eq_plus_compat a
             (real_plus (real_opp b) (real_plus b (real_opp c0)))
             a (real_opp c0)
             (real_eq_refl a)
             (real_eq_trans
                (real_plus (real_opp b) (real_plus b (real_opp c0)))
                (real_plus (real_plus (real_opp b) b) (real_opp c0))
                (real_opp c0)
                (real_plus_assoc (real_opp b) b (real_opp c0))
                (real_eq_trans
                   (real_plus (real_plus (real_opp b) b) (real_opp c0))
                   (real_plus real_zero (real_opp c0)) (real_opp c0)
                   (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                      (real_opp c0) real_zero (real_opp c0)
                      (real_eq_trans (real_plus (real_opp b) b)
                         (real_plus b (real_opp b)) real_zero
                         (real_plus_comm (real_opp b) b) (real_plus_opp b))
                      (real_eq_refl (real_opp c0)))
                   (kv_plus_zero_l (real_opp c0))))).
Qed.

(* |a − b| == |b − a| *)
Lemma kv_abs_minus_flip : forall a b : Real,
  real_eq (real_abs (real_minus_r a b)) (real_abs (real_minus_r b a)).
Proof.
  intros a b.
  apply (real_eq_trans
           (real_abs (real_minus_r a b))
           (real_abs (real_opp (real_minus_r a b)))
           (real_abs (real_minus_r b a))).
  - exact (real_eq_sym (real_abs (real_opp (real_minus_r a b)))
             (real_abs (real_minus_r a b))
             (real_abs_opp (real_minus_r a b))).
  - apply real_abs_eq_compat.
    apply (real_eq_trans
             (real_opp (real_plus a (real_opp b)))
             (real_plus (real_opp a) (real_opp (real_opp b)))
             (real_plus b (real_opp a))).
    + exact (real_opp_plus a (real_opp b)).
    + apply (real_eq_trans
               (real_plus (real_opp a) (real_opp (real_opp b)))
               (real_plus (real_opp a) b)
               (real_plus b (real_opp a))
               (RealSetoid.real_eq_plus_compat (real_opp a)
                  (real_opp (real_opp b)) (real_opp a) b
                  (real_eq_refl (real_opp a)) (real_opp_opp b))
               (real_plus_comm (real_opp a) b)).
Qed.

(* D 三角（Bishop ε 形）：D(a,c) ≤ D(a,b) + D(b,c) + ε *)
Lemma kv_D_triangle : forall (a b cc : Tok -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (Ddist a cc)
          (real_plus (Ddist a b) (real_plus (Ddist b cc) eps)).
Proof.
  intros a b cc eps Heps.
  assert (Hshare : real_lt real_zero
            (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps))
    by (apply kv_share_pos; exact Heps).
  unfold Ddist.
  apply (real_le_trans
           (real_list_sum Tok
              (fun x : Tok => real_abs (real_minus_r (a x) (cc x))) states)
           (real_list_sum Tok
              (fun x : Tok =>
                 real_plus
                   (real_plus (real_abs (real_minus_r (a x) (b x)))
                              (real_abs (real_minus_r (b x) (cc x))))
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps))
              states)
           (real_plus
              (real_list_sum Tok
                 (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
              (real_plus
                 (real_list_sum Tok
                    (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                 eps))).
  - apply real_list_sum_le. intro x.
    apply (real_le_trans
             (real_abs (real_minus_r (a x) (cc x)))
             (real_abs
                (real_plus (real_minus_r (a x) (b x))
                           (real_minus_r (b x) (cc x))))
             (real_plus
                (real_plus (real_abs (real_minus_r (a x) (b x)))
                           (real_abs (real_minus_r (b x) (cc x))))
                (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                           eps))).
    + apply inr. apply real_abs_eq_compat.
      exact (kv_minus_split (a x) (b x) (cc x)).
    + exact (real_abs_triangle_le_eps (real_minus_r (a x) (b x))
               (real_minus_r (b x) (cc x))
               (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                          eps)
               Hshare).
  - apply inr.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun x : Tok =>
                   real_plus
                     (real_plus (real_abs (real_minus_r (a x) (b x)))
                                (real_abs (real_minus_r (b x) (cc x))))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                states)
             (real_plus
                (real_list_sum Tok
                   (fun x : Tok =>
                      real_plus
                        (real_abs (real_minus_r (a x) (b x)))
                        (real_abs (real_minus_r (b x) (cc x))))
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps)))
             (real_plus
                (real_list_sum Tok
                   (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
                (real_plus
                   (real_list_sum Tok
                      (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                   eps))).
    + apply (real_eq_trans _ _ _
               (real_list_sum_add Tok
                  (fun x : Tok =>
                     real_plus
                       (real_abs (real_minus_r (a x) (b x)))
                       (real_abs (real_minus_r (b x) (cc x))))
                  (fun _ : Tok =>
                     real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                               eps)
                  states)
               (RealSetoid.real_eq_plus_compat
                  (real_list_sum Tok
                     (fun x : Tok =>
                        real_plus
                          (real_abs (real_minus_r (a x) (b x)))
                          (real_abs (real_minus_r (b x) (cc x))))
                     states)
                  (real_list_sum Tok
                     (fun _ : Tok =>
                        real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                  eps)
                     states)
                  (real_list_sum Tok
                     (fun x : Tok =>
                        real_plus
                          (real_abs (real_minus_r (a x) (b x)))
                          (real_abs (real_minus_r (b x) (cc x))))
                     states)
                  (real_mult (real_of_nat (length states))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                  (real_eq_refl _)
                  (kv_sum_const_list Tok
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps) states))).
    + apply (real_eq_trans _ _ _
               (RealSetoid.real_eq_plus_compat
                  (real_list_sum Tok
                     (fun x : Tok =>
                        real_plus
                          (real_abs (real_minus_r (a x) (b x)))
                          (real_abs (real_minus_r (b x) (cc x))))
                     states)
                  (real_mult (real_of_nat (length states))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                  (real_plus
                     (real_list_sum Tok
                        (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
                     (real_list_sum Tok
                        (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states))
                  eps
                  (real_list_sum_add Tok
                     (fun x : Tok => real_abs (real_minus_r (a x) (b x)))
                     (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                  (kv_inv_absorb (real_of_nat (length states)) kv_N_pos eps))
               (real_eq_sym _ _ (real_plus_assoc
                  (real_list_sum Tok
                     (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
                  (real_list_sum Tok
                     (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                  eps))).
Qed.

(* 行误差一步变动（件 4 的核心单步界）：
   D(kv_K_ev μ, K μ) ≤ c + ε（行三角 + 换序 + Hrow + 归一化） *)
(* 加权双重和化简：Σ_s'Σ_s |μ(s)·(kv_K_ev−K)(s,s')| == Σ_s μ(s)·tv_row(s) *)
Lemma kv_dsum_row_err : forall mu : Tok -> Real,
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_eq (real_list_sum Tok
             (fun s' : Tok =>
                real_list_sum Tok
                  (fun s : Tok =>
                     real_abs
                       (real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s'))))
                  states)
              states)
          (real_list_sum Tok
             (fun s : Tok => real_mult (mu s) (tv_row s)) states).
Proof.
  intros mu Hnn.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s'))))
                   states)
              states)
           (real_list_sum Tok
              (fun s : Tok =>
                 real_list_sum Tok
                   (fun s' : Tok =>
                      real_abs
                        (real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s'))))
                   states)
              states) _).
  - apply kv_swap_list.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_abs
                     (real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s'))))
                states)
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_mult (mu s)
                     (real_abs (real_minus_r (K s s') (kv_K_ev s s'))))
                states)
             (real_mult (mu s) (tv_row s))).
    + apply real_list_sum_ext. intro s'.
      apply (real_eq_trans
               (real_abs
                  (real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s'))))
               (real_mult (real_abs (mu s))
                          (real_abs (real_minus_r (kv_K_ev s s') (K s s'))))
               (real_mult (mu s)
                          (real_abs (real_minus_r (K s s') (kv_K_ev s s'))))).
      * exact (real_abs_mult_req (mu s)
                 (real_minus_r (kv_K_ev s s') (K s s'))).
      * apply (RealSetoid.real_eq_mult_compat (real_abs (mu s))
                 (real_abs (real_minus_r (kv_K_ev s s') (K s s')))
                 (mu s)
                 (real_abs (real_minus_r (K s s') (kv_K_ev s s')))
                 (kv_abs_nonneg_id (mu s) (Hnn s))
                 (kv_abs_minus_flip (kv_K_ev s s') (K s s'))).
    + apply real_list_sum_linear.
Qed.

(* 行误差一步变动（件 4 的核心单步界）：
   D(kv_K_ev μ, K μ) ≤ c + ε（行三角 + 换序 + Hrow + 归一化） *)
Lemma kv_step_drift : forall (mu : Tok -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_le (Ddist (lstep kv_K_ev mu) (lstep K mu)) (real_plus c eps).
Proof.
  intros mu eps Heps Hnorm Hnn.
  assert (Hshare : real_lt real_zero
            (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps))
    by (apply kv_share_pos; exact Heps).
  unfold Ddist.
  apply (real_le_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (lstep kv_K_ev mu s') (lstep K mu s'))) states)
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_abs
                           (real_mult (mu s)
                                      (real_minus_r (kv_K_ev s s') (K s s'))))
                      states)
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps))
              states)
           (real_plus c eps)).
  - apply real_list_sum_le. intro s'.
    apply (real_le_trans
             (real_abs (real_minus_r (lstep kv_K_ev mu s') (lstep K mu s')))
             (real_abs
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s'))) states))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (mu s)
                                   (real_minus_r (kv_K_ev s s') (K s s'))))
                   states)
                (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                           eps))).
    + apply inr. apply real_abs_eq_compat.
      exact (kv_lstep2_minus_pt kv_K_ev K mu s').
    + exact (kv_abs_triangle_list_eps Tok
               (fun s : Tok =>
                  real_mult (mu s) (real_minus_r (kv_K_ev s s') (K s s')))
               states (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                  eps) Hshare).
  - apply (real_le_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_abs
                             (real_mult (mu s)
                                        (real_minus_r (kv_K_ev s s') (K s s'))))
                        states)
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                states)
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (mu s) (tv_row s))
                   states)
                eps)
             (real_plus c eps)).
    + apply inr.
      apply (real_eq_trans _ _ _
               (real_list_sum_add Tok
                  (fun s' : Tok =>
                     real_list_sum Tok
                       (fun s : Tok =>
                          real_abs
                            (real_mult (mu s)
                                       (real_minus_r (kv_K_ev s s') (K s s'))))
                       states)
                  (fun _ : Tok =>
                     real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                               eps)
                  states)
               (real_eq_trans _ _ _
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum Tok
                        (fun s' : Tok =>
                           real_list_sum Tok
                             (fun s : Tok =>
                                real_abs
                                  (real_mult (mu s)
                                             (real_minus_r (kv_K_ev s s') (K s s'))))
                             states)
                         states)
                     (real_list_sum Tok
                        (fun _ : Tok =>
                           real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                     eps)
                        states)
                     (real_list_sum Tok
                        (fun s : Tok => real_mult (mu s) (tv_row s)) states)
                     (real_mult (real_of_nat (length states))
                        (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                   eps))
                     (kv_dsum_row_err mu Hnn)
                     (kv_sum_const_list Tok
                        (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                   eps) states))
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum Tok
                        (fun s : Tok => real_mult (mu s) (tv_row s)) states)
                     (real_mult (real_of_nat (length states))
                        (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                   eps))
                     (real_list_sum Tok
                        (fun s : Tok => real_mult (mu s) (tv_row s)) states)
                     eps
                     (real_eq_refl _)
                     (kv_inv_absorb (real_of_nat (length states)) kv_N_pos eps)))).
    + apply (real_le_trans
               (real_plus
                  (real_list_sum Tok (fun s : Tok => real_mult (mu s) (tv_row s))
                     states)
                  eps)
               (real_plus
                  (real_list_sum Tok (fun s : Tok => real_mult (mu s) c) states)
                  eps)
               (real_plus c eps)).
      * apply real_le_plus_compat.
        -- apply real_list_sum_le. intro s.
           apply (real_le_trans
                    (real_mult (mu s) (tv_row s))
                    (real_mult (tv_row s) (mu s))
                    (real_mult (mu s) c)).
           ** apply inr. apply real_mult_comm.
           ** apply (real_le_trans
                        (real_mult (tv_row s) (mu s))
                        (real_mult c (mu s))
                        (real_mult (mu s) c)).
              ++ exact (real_le_mult_compat_weak (tv_row s) c (mu s)
                          (Hnn s) (Hrow s)).
              ++ apply inr. apply real_mult_comm.
        -- apply real_le_refl.
      * apply inr.
        apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum Tok (fun s : Tok => real_mult (mu s) c) states)
                 eps c eps
                 (real_eq_trans _ _ _
                    (real_list_sum_linear_r Tok c mu states)
                    (real_eq_trans _ _ _
                       (RealSetoid.real_eq_mult_compat c
                          (real_list_sum Tok mu states) c real_one
                          (real_eq_refl c) Hnorm)
                       (real_mult_one c)))
                 (real_eq_refl eps)).
Qed.

(* ---------- 件 4：主定理·变动 ---------- *)

(* 望远镜主归纳：a_n ≤ n·c + n·ε0 对任意 ε0 > 0（三分支 ε/3 精确闭合） *)
(* 四项 AC 重排：(a+b)+(c+d) == (a+c)+(real_plus b d)（assoc/comm 纯机械链） *)
Lemma kv_regroup4 : forall a b c0 d : Real,
  real_eq (real_plus (real_plus a b) (real_plus c0 d))
          (real_plus (real_plus a c0) (real_plus b d)).
Proof.
  intros a b c0 d.
  apply (real_eq_trans
           (real_plus (real_plus a b) (real_plus c0 d))
           (real_plus a (real_plus b (real_plus c0 d)))
           (real_plus (real_plus a c0) (real_plus b d))).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans
             (real_plus a (real_plus b (real_plus c0 d)))
             (real_plus a (real_plus c0 (real_plus b d)))
             (real_plus (real_plus a c0) (real_plus b d))).
    + apply (RealSetoid.real_eq_plus_compat a
               (real_plus b (real_plus c0 d))
               a
               (real_plus c0 (real_plus b d))
               (real_eq_refl a)
               (real_eq_trans
                  (real_plus b (real_plus c0 d))
                  (real_plus (real_plus b c0) d)
                  (real_plus c0 (real_plus b d))
                  (real_plus_assoc b c0 d)
                  (real_eq_trans
                     (real_plus (real_plus b c0) d)
                     (real_plus (real_plus c0 b) d)
                     (real_plus c0 (real_plus b d))
                     (RealSetoid.real_eq_plus_compat (real_plus b c0) d
                        (real_plus c0 b) d
                        (real_plus_comm b c0) (real_eq_refl d))
                     (real_eq_sym _ _ (real_plus_assoc c0 b d))))).
    + apply (real_plus_assoc a c0 (real_plus b d)).
Qed.


(* P2 修复路线：kv_regroup4 打头 + assoc 换位 + H3 末端吸收（4 步链）；
   原稿中点 cc+(dd+ee) 处漏一步 (dd+h)+h 的 assoc 归位，全链重排 *)
Lemma kv_assemble_le : forall cc dd h ee : Real,
  real_eq (real_plus h (real_plus h h)) ee ->
  real_eq (real_plus (real_plus cc h) (real_plus (real_plus dd h) h))
          (real_plus (real_plus cc dd) ee).
Proof.
  intros cc dd h ee H3.
  apply (real_eq_trans
           (real_plus (real_plus cc h) (real_plus (real_plus dd h) h))
           (real_plus (real_plus (real_plus cc dd) h) (real_plus h h))
           (real_plus (real_plus cc dd) ee)).
  - apply (real_eq_trans
             (real_plus (real_plus cc h) (real_plus (real_plus dd h) h))
             (real_plus (real_plus cc (real_plus dd h)) (real_plus h h))
             (real_plus (real_plus (real_plus cc dd) h) (real_plus h h))).
    + exact (kv_regroup4 cc h (real_plus dd h) h).
    + exact (RealSetoid.real_eq_plus_compat
               (real_plus cc (real_plus dd h))
               (real_plus h h)
               (real_plus (real_plus cc dd) h)
               (real_plus h h)
               (real_plus_assoc cc dd h) (real_eq_refl (real_plus h h))).
  - apply (real_eq_trans
             (real_plus (real_plus (real_plus cc dd) h) (real_plus h h))
             (real_plus (real_plus cc dd) (real_plus h (real_plus h h)))
             (real_plus (real_plus cc dd) ee)).
    + exact (real_eq_sym _ _
               (real_plus_assoc (real_plus cc dd) h (real_plus h h))).
    + exact (RealSetoid.real_eq_plus_compat
               (real_plus cc dd) (real_plus h (real_plus h h))
               (real_plus cc dd) ee
               (real_eq_refl (real_plus cc dd)) H3).
Qed.

Lemma kv_drift_P : forall (n : nat) (mu : Tok -> Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall eps0 : Real,
  real_lt real_zero eps0 ->
  real_le (Ddist (kev_iter n mu) (k_iter n mu))
          (real_plus (real_mult (real_of_nat n) c)
                     (real_mult (real_of_nat n) eps0)).
Proof.
  intro n. induction n as [| n IH]; intros mu Hnorm Hnn eps0 Heps0.
  - cbn [kev_iter k_iter real_of_nat].
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (Ddist mu mu) real_zero
             (real_plus (real_mult real_zero c) (real_mult real_zero eps0))).
    + exact (kv_D_zero mu).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult real_zero c) (real_mult real_zero eps0))
               (real_plus real_zero real_zero) real_zero).
      * apply (RealSetoid.real_eq_plus_compat (real_mult real_zero c)
                 (real_mult real_zero eps0) real_zero real_zero
                 (real_eq_trans _ _ _ (real_mult_comm real_zero c)
                    (real_mult_zero c))
                 (real_eq_trans _ _ _ (real_mult_comm real_zero eps0)
                    (real_mult_zero eps0))).
      * apply real_plus_zero.
  - cbn [kev_iter k_iter real_of_nat].
    assert (HXn : real_eq (real_list_sum Tok (kev_iter n mu) states) real_one)
      by exact (kv_kev_iter_norm n mu Hnorm).
    assert (HZn : real_eq (real_list_sum Tok (k_iter n mu) states) real_one)
      by exact (kv_k_iter_norm n mu Hnorm).
    assert (HXnn : forall s : Tok, real_le real_zero (kev_iter n mu s))
      by exact (kv_kev_iter_nonneg n mu Hnn).
    assert (Ht3 : real_lt real_zero
              (real_mult (real_inv_pos (real_plus (real_plus real_one real_one)
                                          real_one)
                           kv_three_R_pos) eps0)).
    { apply real_mult_pos_compat.
      - apply real_inv_pos_pos.
      - exact Heps0. }
    (* 3·H == ε0（H = inv3·ε0；kv_inv_absorb 精确闭合） *)
    assert (H3B : real_eq
              (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))) eps0).
    {{ apply (real_eq_trans
               (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
               (real_plus (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
               eps0).
      - apply real_plus_assoc.
      - apply (real_eq_trans
                 (real_plus (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
                 (real_mult (real_plus (real_plus real_one real_one) real_one) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
                 eps0).
        + apply (kv_plus_self_three (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)).
        + exact (kv_inv_absorb (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos eps0). }}
    (* 主链：三角(ε/3) + 行误差(ε/3) + 非扩张(ε/3)，总和恰好 ε0 *)
    apply (real_le_trans _ _ _ (kv_D_triangle
              (lstep kv_K_ev (kev_iter n mu)) (lstep K (kev_iter n mu))
              (lstep K (k_iter n mu)) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) Ht3)).
    + apply (real_le_trans _
               (real_plus
                  (real_plus c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
                  (real_plus (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))))
               _).
      * apply real_le_plus_compat.
        -- exact (real_le_trans _ _ _
                     (kv_step_drift (kev_iter n mu) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) Ht3 HXn HXnn)
                     (inr (RealSetoid.real_eq_plus_compat c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)
                             (real_eq_refl c) (real_eq_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))))).
        -- exact (real_le_trans _ _ _
                     (real_le_plus_compat _ _ _ _
                        (kv_nonexpansive K Krow
                           (fun s s'' : Tok =>
                              real_le_from_lt_aux real_zero (K s s'') (Kpos s s''))
                           (kev_iter n mu) (k_iter n mu) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) Ht3)
                        (real_le_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
                     (real_le_trans _ _ _
                        (real_le_plus_compat _ _ _ _
                           (real_le_plus_compat _ _ _ _
                              (IH mu Hnorm Hnn eps0 Heps0)
                              (real_le_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
                           (real_le_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
                        (inr (real_eq_sym _ _ (real_plus_assoc (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))
                           (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)
                           (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))))).

      * apply (real_le_trans _ (real_plus (real_plus c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))) eps0) _).
        -- exact (real_le_trans _ _ _
                     (inr (kv_regroup4 c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))))
                     (real_le_plus_compat _ _ _ _
                        (real_le_refl (real_plus c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))))
                        (inr H3B))).
        -- apply inr.
           (* P2 路线：assoc → 组内换位 → 再 assoc 的四项重排 + 分配吸收；
             原稿链残留 inv3 项且 kv_one_mult_l 假设位错配，整链重写 *)
           apply (real_eq_trans
                    (real_plus (real_plus c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))) eps0)
                    (real_plus (real_plus c (real_mult (real_of_nat n) c)) (real_plus eps0 (real_mult (real_of_nat n) eps0)))
                    (real_plus (real_mult (real_plus real_one (real_of_nat n)) c) (real_mult (real_plus real_one (real_of_nat n)) eps0))
                    (real_eq_trans _ _ _
                       (real_eq_sym _ _ (real_plus_assoc c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) eps0))
                       (real_eq_trans _ _ _
                          (RealSetoid.real_eq_plus_compat c
                             (real_plus (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) eps0)
                             c
                             (real_plus (real_mult (real_of_nat n) c) (real_plus (real_mult (real_of_nat n) eps0) eps0))
                             (real_eq_refl c)
                             (real_eq_sym _ _ (real_plus_assoc (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0) eps0)))
                          (real_eq_trans _ _ _
                             (RealSetoid.real_eq_plus_compat c
                                (real_plus (real_mult (real_of_nat n) c) (real_plus (real_mult (real_of_nat n) eps0) eps0))
                                c
                                (real_plus (real_mult (real_of_nat n) c) (real_plus eps0 (real_mult (real_of_nat n) eps0)))
                                (real_eq_refl c)
                                (RealSetoid.real_eq_plus_compat (real_mult (real_of_nat n) c)
                                   (real_plus (real_mult (real_of_nat n) eps0) eps0)
                                   (real_mult (real_of_nat n) c)
                                   (real_plus eps0 (real_mult (real_of_nat n) eps0))
                                   (real_eq_refl (real_mult (real_of_nat n) c))
                                   (real_plus_comm (real_mult (real_of_nat n) eps0) eps0)))
                             (real_plus_assoc c (real_mult (real_of_nat n) c) (real_plus eps0 (real_mult (real_of_nat n) eps0))))))
                    (RealSetoid.real_eq_plus_compat
                       (real_plus c (real_mult (real_of_nat n) c)) (real_plus eps0 (real_mult (real_of_nat n) eps0))
                       (real_mult (real_plus real_one (real_of_nat n)) c) (real_mult (real_plus real_one (real_of_nat n)) eps0)
                       (real_eq_trans _ _ _
                          (RealSetoid.real_eq_plus_compat c (real_mult (real_of_nat n) c)
                             (real_mult real_one c) (real_mult (real_of_nat n) c)
                             (real_eq_sym _ _ (kv_one_mult_l c))
                             (real_eq_refl (real_mult (real_of_nat n) c)))
                          (real_eq_sym _ _ (kv_distrib_r real_one (real_of_nat n) c)))
                       (real_eq_trans _ _ _
                          (RealSetoid.real_eq_plus_compat eps0 (real_mult (real_of_nat n) eps0)
                             (real_mult real_one eps0) (real_mult (real_of_nat n) eps0)
                             (real_eq_sym _ _ (kv_one_mult_l eps0))
                             (real_eq_refl (real_mult (real_of_nat n) eps0)))
                          (real_eq_sym _ _ (kv_distrib_r real_one (real_of_nat n) eps0))))).

Qed.

(* ===================== 件 4 主结果：变动界（Bishop ε 形） ==================
   前提 Hrow（一致行误差常数）下，双核迭代 n 步的 TV 变动 ≤ n·c + ε。 *)
Theorem kv_drift_bound : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  real_le (Ddist (kev_iter n mu) (k_iter n mu))
          (real_plus (real_mult (real_of_nat n) c) eps).
Proof.
  intros n mu eps Hnorm Hnn Heps.
  destruct n as [| m].
  - cbn [kev_iter k_iter real_of_nat].
    (* P2 修复：基例 0 == 0·c+eps 不成立；正链 D=0 ≤ eps == 0·c+eps *)
    apply (real_le_trans _ eps _).
    + apply (real_le_trans _ real_zero _).
      * apply RealSetoid.real_eq_le. exact (kv_D_zero mu).
      * apply real_le_from_lt_aux. exact Heps.
    + apply inr.
      apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult real_zero c) eps)
               (real_plus real_zero eps)
               eps).
      * exact (RealSetoid.real_eq_plus_compat (real_mult real_zero c) eps
                 real_zero eps
                 (real_eq_trans _ _ _ (real_mult_comm real_zero c)
                    (real_mult_zero c))
                 (real_eq_refl eps)).
      * apply kv_plus_zero_l.
  - assert (Hshare : real_lt real_zero
              (real_mult (real_inv_pos (real_of_nat (Datatypes.S m))
                           (kv_ofnat_S_pos m)) eps))
      by (apply real_mult_pos_compat;
          [apply real_inv_pos_pos | exact Heps]).
    apply (real_le_trans
             (Ddist (kev_iter (Datatypes.S m) mu) (k_iter (Datatypes.S m) mu))
             (real_plus (real_mult (real_of_nat (Datatypes.S m)) c)
                        (real_mult (real_of_nat (Datatypes.S m))
                           (real_mult
                              (real_inv_pos (real_of_nat (Datatypes.S m))
                                           (kv_ofnat_S_pos m)) eps)))
             (real_plus (real_mult (real_of_nat (Datatypes.S m)) c) eps)).
    + exact (kv_drift_P (Datatypes.S m) mu Hnorm Hnn _ Hshare).
    + apply (RealSetoid.real_le_id_r _ _ _
               (RealSetoid.real_eq_plus_compat
                  (real_mult (real_of_nat (Datatypes.S m)) c)
                  (real_mult (real_of_nat (Datatypes.S m))
                     (real_mult (real_inv_pos (real_of_nat (Datatypes.S m))
                                (kv_ofnat_S_pos m)) eps))
                  (real_mult (real_of_nat (Datatypes.S m)) c)
                  eps
                  (real_eq_refl (real_mult (real_of_nat (Datatypes.S m)) c))
                  (kv_inv_absorb (real_of_nat (Datatypes.S m))
                     (kv_ofnat_S_pos m) eps))).
      apply real_le_refl.
Qed.


Theorem kv_drift_bound_tv : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  real_le (tvL (kev_iter n mu) (k_iter n mu))
          (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                     (real_plus (real_mult (real_of_nat n) c) eps)).
Proof.
  intros n mu eps Hnorm Hnn Heps. unfold tvL.
  apply real_le_mult_compat_r.
  - apply real_le_from_lt_aux. apply real_inv_pos_pos.
  - exact (kv_drift_bound n mu eps Hnorm Hnn Heps).
Qed.

End UpKVDrift.


Extraction "upkvdrift_probe.ml" kv_Z_keep kv_K_ev tail_row tv_row kev_iter k_iter
  lstep Ddist tvL
  kv_kev_row_one kv_ZK_le_one kv_invZ_ge_one
  kev_row_tv_exact kev_row_tv_bound kev_row_tv_one_minus_Z
  kv_drift_bound kv_drift_bound_tv.
(* ================= §2 p2t1_pos_const_core 族 ================= *)
From Stdlib Require Import QArith.QArith.

(* ############# 段一：Real 载体证书共享核（Q 层乘法保序全参显式） ########### *)
(* 体例同族件：p1t1_beta_pos_supply／p1t1_eta_le_one_supply（同构语句形）。   *)
(*   real_lt 逐点展开，eps 取 q/2；Q 层乘法保序走全参显式项。                 *)
(*   束间共享核，逐位行以具名引理直引到位。                                   *)

Theorem p2t1_pos_const_core : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof.
  intros q Hq.
  assert (Hq' : Qlt (0#1)%Q q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  unfold real_lt.
  exists (q * (1#2)%Q).
  split.
  - apply Qlt_to_QltT.
    assert (H2 : Qlt (0 * (1#2)%Q) (q * (1#2)%Q)).
    { exact (Qmult_lt_compat_r 0%Q q (1#2)%Q H02 Hq'). }
    setoid_rewrite Qmult_0_l in H2. exact H2.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hc. setoid_rewrite Hz.
    assert (Hr1 : (q - 0)%Q == (1#1)%Q * q) by ring. setoid_rewrite Hr1.
    assert (Hr2 : q * (1#2)%Q == (1#2)%Q * q) by ring. setoid_rewrite Hr2.
    exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q q Hq' Hhalf).
Qed.

Theorem p2t1_le_one_const_core : forall q : Q, QltT q (1#1)%Q ->
  real_le (real_const q) real_one.
Proof.
  intros q Hq.
  assert (Hq' : Qlt q (1#1)%Q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  assert (H0m : Qlt 0%Q (1 - q)%Q)
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (H0 : Qlt 0 ((1#1)%Q + (- q)))
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (Hlt : real_lt (real_const q) real_one).
  { unfold real_lt.
    exists ((1 - q) * (1#2)%Q)%Q.
    split.
    - apply Qlt_to_QltT.
      assert (H2a : Qlt (0 * (1#2)%Q) ((1 - q)%Q * (1#2)%Q)).
      { exact (Qmult_lt_compat_r 0%Q (1 - q)%Q (1#2)%Q H02 H0m). }
      setoid_rewrite Qmult_0_l in H2a. exact H2a.
    - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
      assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
      assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc. setoid_rewrite Ho.
      assert (HrB : (1 - q)%Q == (1#1)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrB at 2.
      assert (HrA : (1 - q)%Q * (1#2)%Q
                    == (1#2)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrA.
      exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q ((1#1)%Q + (- q)) H0 Hhalf). }
  unfold real_le.
  exact (@inl (real_lt (real_const q) real_one)
              (real_eq (real_const q) real_one) Hlt).
Qed.

(* 端点双供（p1t1 端点形同款） *)
Theorem p2t1_one_pos_lt : real_lt real_zero real_one.
Proof. exact real_lt_zero_one. Qed.

Theorem p2t1_one_le_one : real_le real_one real_one.
Proof. exact (real_le_refl real_one). Qed.

(* ################ 段二：逐位供给·正性数据位行（核直引到位） ############### *)
(* 行 1/2：T／T_pos（FEPAttention 温度数据位与正性配对）。                    *)
(* 行 3：D_pos（热力学温度正性，两区段同形）。                                *)
(* 行 6：Delta_pos（双界 logits 上界正性）。                                  *)
(* 行 7：temp_pos（RowView 区 12 位组）。                                     *)
(* 行 10：min_p_pos（Min-P 超参正性，两节各一套，一证双覆盖）。               *)
(* 行 12：temperature_pos（采样温度正性三区段）。                             *)
(* 行 18：q_pos（参考策略逐点正——常值函数载体）。                            *)
(* 行 11：min_p_lt_one（Min-P 上界位——序界核直引）。                         *)
(* 行 24：lt_minus_nonneg（序差正性——real_lt 逐点展开）。                    *)

Theorem p2t1_T_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

(* 行 2 载体：T 取正有理常数载体 *)
Definition p2t1_T_c (q : Q) : Real := real_const q.

Theorem p2t1_T_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (p2t1_T_c q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_D_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_Delta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_temp_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_min_p_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_temperature_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

(* 行 18：q 取常值函数载体，逐点正性由核直引 *)
Theorem p2t1_q_pos_supply : forall (q : Q), QltT (0#1)%Q q ->
  forall (S0 : Set) (s : S0),
    real_lt real_zero ((fun _ : S0 => real_const q) s).
Proof. intros q Hq S0 s. exact (p2t1_pos_const_core q Hq). Qed.

(* 行 11：min_p 取 (0,1) 内有理见证，不超过一由序界核直引 *)
Theorem p2t1_min_p_lt_one_supply : forall q : Q, QltT q (1#1)%Q ->
  real_le (real_const q) real_one.
Proof. intros q Hq. exact (p2t1_le_one_const_core q Hq). Qed.

(* 行 24：real_const 对的序差正性（real_minus_r a b := real_plus a (real_opp b) *)
(*   逐点透明：q2 + (−q1) − 0 ＝ q2 − q1；eps 取 (q2−q1)/2 展开） *)
Theorem p2t1_lt_minus_nonneg_supply : forall q1 q2 : Q, QltT q1 q2 ->
  real_lt real_zero (real_minus_r (real_const q2) (real_const q1)).
Proof.
  intros q1 q2 Hq.
  assert (Hq' : Qlt q1 q2) by (apply QltT_to_Qlt; exact Hq).
  assert (H0m : Qlt 0%Q (q2 - q1)%Q)
    by exact (proj1 (Qlt_minus_iff q1 q2) Hq').
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  unfold real_lt.
  exists ((q2 - q1) * (1#2)%Q)%Q.
  split.
  - apply Qlt_to_QltT.
    assert (H2a : Qlt (0 * (1#2)%Q) ((q2 - q1)%Q * (1#2)%Q)).
    { exact (Qmult_lt_compat_r 0%Q (q2 - q1)%Q (1#2)%Q H02 H0m). }
    setoid_rewrite Qmult_0_l in H2a. exact H2a.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    assert (Hy : projT1 (real_minus_r (real_const q2) (real_const q1)) n
                 == (q2 - q1)%Q).
    { unfold real_minus_r, real_plus, real_opp.
      cbn [projT1 real_const].
      try setoid_rewrite (real_const_proj q2 n).
      try setoid_rewrite (real_const_proj q1 n).
      ring. }
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hy. setoid_rewrite Hz.
    assert (Hr1 : (q2 - q1)%Q - 0 == (1#1)%Q * (q2 - q1)) by ring.
    setoid_rewrite Hr1.
    assert (HrC : (q2 - q1)%Q * (1#2)%Q == (1#2)%Q * (q2 - q1)) by ring.
    setoid_rewrite HrC.
    exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q (q2 - q1) H0m Hhalf).
Qed.

(* ################ 段三：单点 SumOver 实例世界行（T 簇载体） ############### *)
(* 世界：uab_ssUnit＋uab_soUnit（全库唯一具体 SumOver 实例，                  *)
(*   见 Require 面）：和退化为核元素取值。                                 *)
(* 行 17：spp（求和正性函数前提）——单点世界上构造性成立：                     *)
(*   和恒等于 f 于唯一点，前提逐点直取。                                      *)
(* 行 8/9：evicted_partition_pos／topk_kept_partition_pos——保留判定取常真、   *)
(*   保留分支取常一，配分和即一，                                            *)
(*   one_pos 直引（p1t2 B11 形单点世界实现）。                                 *)

Theorem p2t1_spp_supply : forall (RI0 : RealInterfaceEnhanced)
    (f : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0),
    (forall s : @S RI0 (@uab_ssUnit (@RI_base RI0)),
       @lt RI0 (@zero RI0) (f s)) ->
    @lt RI0 (@zero RI0)
      (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0))
         (@uab_soUnit (@RI_base RI0)) f).
Proof.
  intros RI0 f H.
  exact (H (@uab_ssUnit_elem (@RI_base RI0))).
Qed.

(* 行 8 载体：保留判定常真＋保留分支常一的逐出配分（单点世界） *)
Definition p2t1_keep_true (RI0 : RealInterfaceEnhanced)
  (_ : @S RI0 (@uab_ssUnit (@RI_base RI0))) : bool := true.
Definition p2t1_bf_one (RI0 : RealInterfaceEnhanced)
  (_ : @S RI0 (@uab_ssUnit (@RI_base RI0))) : @R RI0 := @one RI0.
Definition p2t1_evict_part_c (RI0 : RealInterfaceEnhanced) : @R RI0 :=
  @sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
    (fun s : @S RI0 (@uab_ssUnit (@RI_base RI0)) =>
       if p2t1_keep_true RI0 s then p2t1_bf_one RI0 s else @zero RI0).

Theorem p2t1_evicted_partition_pos_supply : forall RI0 : RealInterfaceEnhanced,
  @lt RI0 (@zero RI0) (p2t1_evict_part_c RI0).
Proof. intro RI0. unfold p2t1_evict_part_c. exact (@one_pos RI0). Qed.

(* 行 9 载体：同形（top-k 保留判定常真） *)
Definition p2t1_topk_keep_true (RI0 : RealInterfaceEnhanced)
  (_ : @S RI0 (@uab_ssUnit (@RI_base RI0))) : bool := true.
Definition p2t1_topk_kept_part_c (RI0 : RealInterfaceEnhanced) : @R RI0 :=
  @sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
    (fun s : @S RI0 (@uab_ssUnit (@RI_base RI0)) =>
       if p2t1_topk_keep_true RI0 s then p2t1_bf_one RI0 s else @zero RI0).

Theorem p2t1_topk_kept_partition_pos_supply :
  forall RI0 : RealInterfaceEnhanced,
  @lt RI0 (@zero RI0) (p2t1_topk_kept_part_c RI0).
Proof. intro RI0. unfold p2t1_topk_kept_part_c. exact (@one_pos RI0). Qed.

(* ############# 段四：枚举载体世界行（枚举表与自然数嵌入） ################## *)

(* 二元枚举集载体（与 p1t2_g2 同构，前缀 p2t1_ 区分） *)
Inductive p2t1_tok : Set :=
| T0 : p2t1_tok
| T1 : p2t1_tok.

Definition p2t1_S_enum : list p2t1_tok := T0 :: T1 :: nil.

(* 行 13：vocab_nonempty（实形 Not (Id vocab nil)）——二元枚举表直构          *)
(*   （Not 为 S01 Set 层别名 A -> Empty_set）；索引取字面构造子形＋          *)
(*   空匹配消解（UpAblP2WByPass 同款体例，可转换性成立）。                    *)
(*   注记：配套模块 p2wb_vocab_nonempty（UpAblP2WByPass）在库，与本件           *)
(*   p2t1_vocab_nonempty_supply 并列在册，互不排斥。 *)
Theorem p2t1_vocab_nonempty_supply : Not (Id (cons T0 (cons T1 nil)) nil).
Proof. exact (fun h => match h with end). Qed.

(* 行 14：S_finite_cover（实形 forall s, InT s S_enum）——                    *)
(*   枚举表两支递推直构（InT_here／InT_next，参数全显式）。 *)
Theorem p2t1_S_finite_cover_supply : forall i : p2t1_tok, InT i p2t1_S_enum.
Proof.
  unfold p2t1_S_enum. intro i. destruct i as [| ].
  - apply InT_here.
  - apply InT_next. apply InT_here.
Qed.

(* 行 15：K（容量数据位，nat）——容量取一载体＋                              *)
(*   (1<=K) 的 Set 层 Nat.leb 副本＋嵌入正性。 *)
Definition p2t1_K_supply : nat := 1.

Theorem p2t1_K_leb_true : Id (Nat.leb 1 p2t1_K_supply) true.
Proof. exact (@id_refl _ true). Qed.

(* 行 20：default_token（默认 token 数据位）——常数载体平凡见证 *)
Definition p2t1_default_token_supply : p2t1_tok := T0.

Theorem p2t1_default_token_witness : Id p2t1_default_token_supply T0.
Proof. exact (@id_refl _ T0). Qed.

(* 自然数嵌入 of_nat（计数嵌入形；避开 S01 顶层 S 遮蔽——用 Datatypes.S） *)
Section P2T1EnumPos.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let lt := @lt RI.
Let plus := @plus RI.

Fixpoint p2t1_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (p2t1_of_nat n')
  end.

(* 行 15：枚举表长度二的嵌入＝一加一，正和字段直引 *)
Theorem p2t1_K_of_nat_pos :
  lt zero (p2t1_of_nat (length p2t1_S_enum)).
Proof.
  unfold p2t1_S_enum.
  apply (lt_id_r zero (plus one one)).
  - exact (id_cong (fun w : R => plus one w) (id_sym (plus_zero one))).
  - apply plus_positive.
    + exact one_pos.
    + exact one_pos.
Qed.

End P2T1EnumPos.

(* ################ 段五：接口前提行（直引形与显式前提形） ################### *)
(* 直引形体例（p1t2 段四同款）：常量载体配分和正性。行 4/5/23 三件            *)
(*   （Setoid 语境）移段七置尾——Import RealInterfaceEnhancedMod 会遮蔽       *)
(*   类字段投影（@one 类型不合期望），沿用同款节序：@形件在前、               *)
(*   Setoid 节在尾。                                                         *)

(* 行 19：q_norm（实形 Id (sum_over_S q) one）——接口面不可构造，              *)
(*   显式前提形（p1t2 B12 同形；具体载体实例＝req 层 boltzmann 归一化件）      *)
Theorem p2t1_q_norm_pack : forall (RI0 : RealInterfaceEnhanced)
    (SS0 : StateSpace RI0) (SO0 : SumOver RI0 SS0) (q : @S RI0 SS0 -> @R RI0),
    Id (@sum_over_S RI0 SS0 SO0 q) (@one RI0) ->
    Id (@sum_over_S RI0 SS0 SO0 q) (@one RI0).
Proof. intros RI0 SS0 SO0 q Hn. exact Hn. Qed.

(* 行 16：topk_pickmax_head（实形）——显式前提形；前提 (1 <= K)%nat 为裸       *)
(*   命题面，改以 Set 层 Nat.leb 副本（Nat.leb_le 双向桥），                  *)
(*   keep/pick 以函数参量全称化（出节签名如实保留）。 *)
Theorem p2t1_topk_pickmax_head_pack :
  forall (Tok0 : Set)
         (keep : forall (K : nat) (prefix : list Tok0), Tok0 -> Set)
         (pick : list Tok0 -> Tok0),
    (forall (K : nat) (prefix : list Tok0),
       Id (Nat.leb 1 K) true -> keep K prefix (pick prefix)) ->
    forall (K : nat) (prefix : list Tok0),
       Id (Nat.leb 1 K) true -> keep K prefix (pick prefix).
Proof. intros Tok0 keep pick H K prefix HK. exact (H K prefix HK). Qed.

(* 行 21：Hrow（UpKVDrift，c 配对）——c 取常数载体 real_one；                 *)
(*   一致行误差前提以 tv_row 展开体（real_list_sum∘real_abs∘real_minus_r）    *)
(*   显式 forall 前提形（出节签名同构）。 *)
Definition p2t1_Hrow_c_supply : Real := real_one.

Theorem p2t1_Hrow_pack : forall (Tok0 : Set) (states : list Tok0)
    (Kk : Tok0 -> Tok0 -> Real) (kv : Tok0 -> Tok0 -> Real) (c : Real),
    (forall s : Tok0,
       real_le (real_list_sum Tok0
                  (fun s' : Tok0 => real_abs (real_minus_r (Kk s s') (kv s s')))
                  states) c) ->
    forall s : Tok0,
       real_le (real_list_sum Tok0
                  (fun s' : Tok0 => real_abs (real_minus_r (Kk s s') (kv s s')))
                  states) c.
Proof. intros Tok0 states Kk kv c Hrow s. exact (Hrow s). Qed.

(* 行 22：Z_temp_spec（参数形之 Real 载体对应面）——real_Z_temp_pos             *)
(*   （UpReqTempDefs）在库直引（五参泛化形）；spec 恒等式面＝                *)
(*   real_Z_temp 定义性展开（定义件头注自书「spec 退化定义性相等」）。        *)
Theorem p2t1_Z_temp_pos_supply : forall (S0 : Type) (sumf : (S0 -> Real) -> Real),
    (forall f : S0 -> Real,
       (forall s : S0, real_lt real_zero (f s)) -> real_lt real_zero (sumf f)) ->
    forall (T : Real) (T_pos : real_lt real_zero T) (energy : S0 -> Real),
      real_lt real_zero (real_Z_temp S0 sumf T T_pos energy).
Proof.
  intros S0 sumf Hsum T T_pos energy.
  exact (real_Z_temp_pos S0 sumf Hsum T T_pos energy).
Qed.

(* 行 25：real_minp_temp_sum_pos（实形）——显式 forall 前提形                 *)
(*   （截断和展开体逐字；保留判定取 Or/inl-inr S01 别名面，与 S08 同构）。 *)
Theorem p2t1_real_minp_temp_sum_pos_pack :
  forall (Token0 : Set) (vocab : list Token0) (tf : Token0 -> Real)
         (keep : list Token0 -> Token0 -> Set)
         (kdec : forall (prefix : list Token0) (w : Token0),
                   Or (keep prefix w) (Not (keep prefix w))),
    (forall prefix : list Token0,
       real_lt real_zero
         (real_list_sum Token0 (fun w : Token0 =>
            match kdec prefix w with
            | inl _ => tf w
            | inr _ => real_zero
            end) vocab)) ->
    forall prefix : list Token0,
       real_lt real_zero
         (real_list_sum Token0 (fun w : Token0 =>
            match kdec prefix w with
            | inl _ => tf w
            | inr _ => real_zero
            end) vocab).
Proof. intros Token0 vocab tf keep kdec Hsum prefix. exact (Hsum prefix). Qed.

(* ################ 段六：证书链升格位（T1/T3 两件＋T2 未竟注记） ########### *)

(* T1：kv_drift_bound（UpKVDrift）plain-eps 形升格 Bishop 形——               *)
(*   real_le_closure_b_one（UpRealLeB，D:=one 特化，证书 real_lt_zero_       *)
(*   one 在库既有）单步直连（Not/And/sigT 全 Set 别名面）。                   *)
Theorem p2t1_kv_drift_bound_B :
  forall (Tok0 : Set) (states : list Tok0) (Hne : Not (Id states nil))
         (K : Tok0 -> Tok0 -> Real)
         (HKnorm : forall s : Tok0,
            real_eq (real_list_sum Tok0 (fun s' : Tok0 => K s s') states) real_one)
         (Kpos : forall s s' : Tok0, real_lt real_zero (K s s'))
         (keep : Tok0 -> bool)
         (keep_nonempty : sigT (fun s : Tok0 => And (Id (keep s) true) (InT s states)))
         (c : Real)
         (Hrow : forall s : Tok0,
            real_le (tv_row Tok0 states K Kpos keep keep_nonempty s) c)
         (n : nat) (mu : Tok0 -> Real),
    real_eq (real_list_sum Tok0 mu states) real_one ->
    (forall s : Tok0, real_le real_zero (mu s)) ->
    real_le_b (Ddist Tok0 states
                 (kev_iter Tok0 states K Kpos keep keep_nonempty n mu)
                 (k_iter Tok0 states K n mu))
              (real_mult (real_of_nat n) c).
Proof.
  intros Tok0 states Hne K HKnorm Kpos keep keep_nonempty c Hrow n mu Hnorm Hnn.
  apply real_le_closure_b_one. intros eps Heps.
  exact (kv_drift_bound Tok0 states Hne K HKnorm Kpos keep keep_nonempty c Hrow
           n mu eps Hnorm Hnn Heps).
Qed.

(* T3：le_b 乘法因子合成器族（UpReqPowMonoBridge x3d_ 系）补全——             *)
(*   常数因子直引形：c 取常数一，正性证书 real_lt_zero_one 直引               *)
(*   x3d_le_b_mult_r_pos；任意非负 Or 形因子直引形：x3d_le_b_mult_r_         *)
(*   nonneg_or 同参重申。                                                    *)
(*   诚实注记：「纯 B 形无上界版」构造性不通——UpReqPowMonoBridge 自书         *)
(*   B 形非负⟹Or 形反向构造性不通，因子无上界 M 时余量乘出无法压回 eps；      *)
(*   有界版 x3d_le_b_mult_r_nonneg_bnd 在库。此否定性结论如实注记。           *)
Theorem p2t1_x3d_le_b_mult_one : forall a b : Real,
  real_le_b a b -> real_le_b (real_mult a real_one) (real_mult b real_one).
Proof.
  intros a b H.
  exact (x3d_le_b_mult_r_pos a b real_one H real_lt_zero_one).
Qed.

Theorem p2t1_x3d_le_b_mult_r : forall a b c : Real,
  real_le_b a b -> real_le real_zero c ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c H Hc.
  exact (x3d_le_b_mult_r_nonneg_or a b c H Hc).
Qed.

(* T2 未竟注记：UpRealLeB 结论 9(e)/(f) 复合/多 eps 形升格面——源件面          *)
(*   real_abs_le_quad_eps 五前提＋四分支内件链（real_abs_le_quad_ll/_le       *)
(*   等），UpRealLeB 尾注自书「可升格但证书链长且语句须前提位改造——未建」；    *)
(*   结论 10 的 plain-eps 面已在库。本件不虚报升格，如实留待后续工作。         *)
(*   本件与在库升格件分工明确，互不重叠。                                     *)

(* ################ 段七：Setoid 语境行（置尾节） ########################### *)
(* 直引形体例：req 系 Setoid 语境，常量载体配分和正性。                       *)
(* 行 4：Z_pos（配分和正性直引）。                                           *)
(* 行 5：Z_thermo_pos（注意力侧热力学配分同形）。                             *)

Import RealInterfaceEnhancedMod.

Section P2T1ReqConst.

Context {R0 : Set} {RIS : RealInterfaceEnhancedSetoid R0}.

Theorem p2t1_Z_pos_supply :
  forall (S0 : Set) (sumf : (S0 -> R0) -> R0) (base_loss : S0 -> R0) (D0 : R0),
    (forall f : S0 -> R0, (forall s : S0, lt zero (f s)) -> lt zero (sumf f)) ->
    forall HDpos : lt zero D0,
      lt zero (sumf (fun s : S0 =>
               exp_neg (mult (inv_pos D0 HDpos) (base_loss s)))).
Proof.
  intros S0 sumf base_loss D0 Hfsum HDpos.
  apply Hfsum.
  intro s.
  apply exp_neg_pos.
Qed.

(* 行 5：Z_thermo 形（energy 命名对位 boltzmann_factor 展开体） *)
Theorem p2t1_Z_thermo_pos_supply :
  forall (S0 : Set) (sumf : (S0 -> R0) -> R0) (energy : S0 -> R0) (D0 : R0),
    (forall f : S0 -> R0, (forall s : S0, lt zero (f s)) -> lt zero (sumf f)) ->
    forall HDpos : lt zero D0,
      lt zero (sumf (fun s : S0 =>
               exp_neg (mult (inv_pos D0 HDpos) (energy s)))).
Proof.
  intros S0 sumf energy D0 Hfsum HDpos.
  exact (p2t1_Z_pos_supply S0 sumf energy D0 Hfsum HDpos).
Qed.

(* 行 23：inv_pos_lt_compat（实形）——接口面不可构造，                        *)
(*   显式前提形（p1t2 B12 同形；req 系同名字段副本）。 *)
Theorem p2t1_inv_pos_lt_compat_pack :
  forall (a b : R0) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha) ->
    lt (inv_pos b Hb) (inv_pos a Ha).
Proof. intros a b Ha Hb Hlt Hit. exact Hit. Qed.

End P2T1ReqConst.

(* ################ 收尾：提取与假设自检 #################################### *)
(* 提取见证面取 Q 层纯函数（零 Real 实例闭包依赖）。 *)
Definition p2t1_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1_g3out".
Extraction "p2t1_G3_Cert.ml" p2t1_g3_pick.

(* ---- 假设审计段（文尾逐件） ---- *)
Print Assumptions p2t1_pos_const_core.
Print Assumptions p2t1_le_one_const_core.
Print Assumptions p2t1_one_pos_lt.
Print Assumptions p2t1_one_le_one.
Print Assumptions p2t1_T_pos_supply.
Print Assumptions p2t1_T_supply.
Print Assumptions p2t1_D_pos_supply.
Print Assumptions p2t1_Delta_pos_supply.
Print Assumptions p2t1_temp_pos_supply.
Print Assumptions p2t1_min_p_pos_supply.
Print Assumptions p2t1_temperature_pos_supply.
Print Assumptions p2t1_q_pos_supply.
Print Assumptions p2t1_min_p_lt_one_supply.
Print Assumptions p2t1_lt_minus_nonneg_supply.
Print Assumptions p2t1_spp_supply.
Print Assumptions p2t1_evicted_partition_pos_supply.
Print Assumptions p2t1_topk_kept_partition_pos_supply.
Print Assumptions p2t1_vocab_nonempty_supply.
Print Assumptions p2t1_S_finite_cover_supply.
Print Assumptions p2t1_K_leb_true.
Print Assumptions p2t1_K_of_nat_pos.
Print Assumptions p2t1_default_token_witness.
Print Assumptions p2t1_Z_pos_supply.
Print Assumptions p2t1_Z_thermo_pos_supply.
Print Assumptions p2t1_inv_pos_lt_compat_pack.
Print Assumptions p2t1_q_norm_pack.
Print Assumptions p2t1_topk_pickmax_head_pack.
Print Assumptions p2t1_Hrow_pack.
Print Assumptions p2t1_Z_temp_pos_supply.
Print Assumptions p2t1_real_minp_temp_sum_pos_pack.
Print Assumptions p2t1_kv_drift_bound_B.
Print Assumptions p2t1_x3d_le_b_mult_one.
Print Assumptions p2t1_x3d_le_b_mult_r.

(* 替换验证位：对替换代表件做假设面核验（零承认件句式自证） *)
Print Assumptions p2t1_pos_const_core.
Print Assumptions p2t1_T_pos_supply.
Print Assumptions p2t1_min_p_lt_one_supply.
