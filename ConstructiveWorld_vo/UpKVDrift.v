(* ============================================================ *)
(* ToyR 玩具证替换件 —— T252 台账席 战役包M（tier2 批量面第三批）    *)
(* 本件为消融落件：原件全文逐字保留，仅将下列定理之证明体替换为    *)
(* 玩具证（实质非平凡三口径：定义层受控展开、显式见证直取、结构性  *)
(* 重演；逐刀金标准文本程序直取自母本体并断言同文），声明面与引用  *)
(* 面零改动，零新增 Require，证尾记号逐件守恒，纯构造性收口，文尾  *)
(* 保留原件假设面追印。清单：                                      *)
(*   kv_N_R_pos（kv_N_R 定义性展开后 kv_N_pos 母本体就地重演：       *)
(*       states 归纳＋空表矛盾支＋尾表 kv_ofnat_S_pos 收口）         *)
(* ============================================================ *)

(* ============================================================ *)
(* UpKVDrift.v *)
(* *)
(* 目的： 核漂移链：行 TV 界与显式迭代预算（Real 层，eps-Bishop 形态）。 *)
(* 主件： tv_row / lstep 行 TV 单步界与 kv_Z_keep_pos / kv_N_R_pos 正性族。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： Real 层三角不等式仅有逐 eps 形态，故取 eps-Bishop 显式假设形态；核行随机与严格正为 Variable 前提。 *)
(* ============================================================ *)

(* ========================================================================= *)
(* UpKVDrift.v — §6 KV 逐出 × 双点收缩：逐出变动动力学定理（件 3/4）        *)
(*                                                                           *)
(* 分工（主会话钉死）：本文件承接方案四的后半——件 3（行 TV 界）与          *)
(* 件 4（主定理·变动）；世界定义/K_ev/Z_keep 照抄契约在文件内重建（独立     *)
(* Section，与新席 UpKVEv.v 各持一份同形定义，既定分工）。                  *)
(*                                                                           *)
(* 世界（list 词表，Real 层，镜像 AttnHardLimit 瘦身形态）：                 *)
(*   Tok : Set + states : list Tok（非空）+ 完整核 K（行归一 + 逐点正）     *)
(*   + keep : Tok -> bool（Set 层判定）+ Z_keep/K_ev 契约定义。             *)
(*                                                                           *)
(* 件 3  kev_row_tv_exact / kev_row_tv_bound / kev_row_tv_one_minus_Z：     *)
(*   tv_row(s) := Σ_{s'}|K(s,s') − K_ev(s,s')| 的精确恒等式                 *)
(*     tv_row(s) == tail_row(s) + tail_row(s)   （tail_row := Σ_drop K）    *)
(*   纸笔推导：keep 支 |K − K_ev| == K_ev − K（符号证书 K ≤ K·invZ，       *)
(*   因 invZ ≥ 1），drop 支 == K；分部求和                                   *)
(*   Σ_keep(K·invZ − K) == (invZ−1)·Z_keep == 1 − Z_keep == tail_row，      *)
(*   drop 支 == tail_row，合计 == 2·tail_row == 2·(1 − Z_keep)——精确最简   *)
(*   形态（强于任务书预案的 ≤ 形态，以等式结果；≤ 形态与 1−Z 形态并列）。  *)
(*                                                                           *)
(* 件 4  kv_drift_bound（主定理·变动）：                                    *)
(*   前提 Hrow : ∀s, tv_row(s) ≤ c（一致行误差常数，规避 sup），对任意      *)
(*   归一化非负 μ 与任意 n、任意 eps > 0：                                   *)
(*     D(K_ev^n μ, K^n μ) ≤ n·c + eps（D := Σ|−| 逐和形态）                 *)
(*   望远镜归纳 a_{n+1} ≤ a_n + c + eps0：中项取 K(K_ev^n μ)，拆            *)
(*     TV(K_ev X, K Z) ≤ TV(K_ev X, K X) + TV(K X, K Z)（三角）             *)
(*     ≤ (c + ε/3) + (a_n + ε/3) + ε/3（行误差 + K 非扩张）——三分支 ε/3    *)
(*   经 3·(ε0/3) == ε0 吸收精确闭合 (S n)·ε0。                              *)
(*                                                                           *)
(* 诚实边界（eps-Bishop 形态的必然性）：Real 层 |a+b| ≤ |a|+|b| 只有逐 eps  *)
(*   形（real_abs_triangle_le_eps；根内 RealSetoid 接口即 Bishop 逐 eps 惯  *)
(*   例），exact le 为 Or(lt,eq) 编码，exact 三角构造性不可得。故件 3 全程  *)
(*   exact（符号证书绕开三角），件 4 为 Bishop 逐 eps 形 ≤ n·c + eps——      *)
(*   与根内 real_abs_nonneg_le_eps 同一诚实档位。TV(inv2·Σ|−|) 同构形态    *)
(*   以 kv_drift_bound_tv 并列结果。                                        *)
(*                                                                           *)
(* 红线自审：纯构造性（零公理/零弃证/零经典逻辑）；语句全 Set 层            *)
(*   （real_eq/real_lt/real_le/Id/InT 均 Set 编码，keep 判定 bool）；       *)
(*   keep_nonempty 契约占位以 sigT/And/Id/InT 落地；全部 Qed。              *)
(* ========================================================================= *)

Require Import CW_ConstructiveWorld_219.

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
(* 会产出 2 处 Obj.magic，故不复用；构造对齐成果存档 UpKVEv.v）。  *)
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

(* kv_Z_keep 正性——升级为定理（对齐 UpKVEv.v：keep 见证项 K(s,s0) > 0
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

(* 均匀分布与 δ minorization 前提（对齐 UpKVEv.v 结果契约：delta_minor
   对裸 K 逐点，不可省——数学修正警报已吸收）。件 3/4 的语句不消费
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

(* 逐和 TV（任务书许可的逐和形态） *)
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


From Stdlib Require Import Extraction.
Extraction "upkvdrift_probe.ml" kv_Z_keep kv_K_ev tail_row tv_row kev_iter k_iter
  lstep Ddist tvL
  kv_kev_row_one kv_ZK_le_one kv_invZ_ge_one
  kev_row_tv_exact kev_row_tv_bound kev_row_tv_one_minus_Z
  kv_drift_bound kv_drift_bound_tv.