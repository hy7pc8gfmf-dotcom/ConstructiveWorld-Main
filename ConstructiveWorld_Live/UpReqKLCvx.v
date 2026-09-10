(* ============================================================ *)
(* UpReqKLCvx.v —— 槽放电波 G7：KL 凸性族收尾席（普查 A 档 7 槽）   *)
(*   范本：UpReqGeomD.v（22 件四关绿）；引擎：CW219 根 + 全在盘     *)
(* ---------------------------------------------------------------- *)
(* 逐槽判定（普查 A 档表 7 行，sed 实读为准）：                      *)
(*   [跳过] UpReqAlign:430 req_step_kl_eta_bound —— step_kl 主件     *)
(*     已由 UpReqGeomD.geod_step_kl_eta_bound_eps（接口形 eps-le）   *)
(*     放电；plain-le 收口属 Or 形精确收口=X 红线（GeomD 诚实边界    *)
(*     节已判），防重复不重建。                                      *)
(*   [阻塞裁决] UpReqAlign:434 req_backward_kl_identity（req 等式）  *)
(*     与 UpReqAlign:630 req_policy_improvement_mono（plain le）——   *)
(*     两槽同属 UpReqAlign softmax-KL 对齐深链（文件内注释自记       *)
(*     「req 重证挂起批 3b」）：需 relative_entropy_req/pi_next_req  *)
(*     经 Z_align^eta 消去的 log-mult 全字段桥——GeomD 头部③已判     *)
(*     「接口字段无 log-mult 全字段故不在其 scope」，同源缺口本席     *)
(*     不越（构造性引擎不在盘，非 timebox 可建）；precise 阻塞词：   *)
(*     softmax-KL 深链 log-mult 接口字段缺口。                       *)
(*   [放电] UpReqAttnGibbs:2146 exp_neg_geo_break —— 阿基米德 N      *)
(*     构造：root exp_lower_q（∃N≥2, e^{−N}<y）+ real_arch +         *)
(*     cauchy_real_exp_mono 全在盘，本席拼链 → klcx_exp_neg_geo_break。 *)
(*   [放电] UpReqAlignRestB:1569 req_boltzmann_diff_bridge —— exp    *)
(*     Lipschitz 桥：root P1 主引理 real_exp_neg_diff_bound@53903    *)
(*     与槽语句逐字同形（req_epos=exp_neg∘opp → Real 层 epos 换形）  *)
(*     → klcx_boltzmann_diff_bridge（纯投影+eq 换形放电）。          *)
(*   [放电] UpReqCauchy:221 r_arch_pow / UpReqAttnIter:163           *)
(*     arch_pow_i —— 几何击穿阿基米德件（Bernoulli + 逆元链）        *)
(*     → klcx_geo_pow_break 统一件 + 两槽镜像实例。                  *)
(* ---------------------------------------------------------------- *)
(* 落点层：Real 实例化定理（载体 Real，real_le/real_lt 即接口        *)
(* RealEnhancedReal 的 le/lt 字段——iface 投影件给出 @le/@lt 语形     *)
(* 出口）。Or 形 plain-le 收口一件未做（判词见上），红线不越。        *)
(* 红线：Set 层语句零 Prop 泄露；全 Qed；既有文件零改；零 git。       *)
(* 编译配方：coqc -Q . "" -Q "..\001" "" UpReqKLCvx.v（cpu_guard 错峰） *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
Require Import CW_ConstructiveWorld_219.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* K-A 环辅件（零名依赖，zero-diff ring 换形；GeomD 同款手法）       *)
(* ============================================================ *)

Lemma klcx_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x. destruct x as [u Hu]. apply real_eq_of_zero_diff.
  intro n. simpl. ring.
Qed.

Lemma klcx_const_one_eq : real_eq (real_const (1 # 1)) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

Lemma klcx_const_two_eq : real_eq (real_const (2 # 1))
                                 (real_plus real_one real_one).
Proof.
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 正因子右乘严格保序（real_lt_mult_compat 的右位形，comm 换形） *)
Lemma klcx_lt_mult_r : forall a b c : Real,
  real_lt real_zero c -> real_lt a b ->
  real_lt (real_mult a c) (real_mult b c).
Proof.
  intros a b c Hc Hab.
  apply (real_lt_eq_lt (real_mult a c) (real_mult c b) (real_mult b c)).
  - apply (real_eq_lt_lt (real_mult a c) (real_mult c a) (real_mult c b)).
    + apply real_mult_comm.
    + exact (real_lt_mult_compat a b c Hc Hab).
  - apply real_mult_comm.
Qed.

(* ============================================================ *)
(* K-B 放电件 1：req_boltzmann_diff_bridge（UpReqAlignRestB:1569）   *)
(*   槽形：|e^{-u}−e^{-v}| ≤ e^{-v}·(|u−v|·epos(|u−v|)+eps)，        *)
(*   epos := exp_neg∘opp（req 层 req_epos 的 Real 层镜像）。          *)
(*   证书链 = root P1 主引理 real_exp_neg_diff_bound 一次喂定。      *)
(* ============================================================ *)

Definition klcx_epos (t : Real) : Real := real_exp_neg (real_opp t).

Lemma klcx_epos_correct : forall t : Real,
  real_eq (klcx_epos t) (cauchy_real_exp t).
Proof.
  intro t. unfold klcx_epos, real_exp_neg.
  apply cauchy_real_exp_wd. apply klcx_opp_opp.
Qed.

Theorem klcx_boltzmann_diff_bridge : forall (u v eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
          (real_mult (real_exp_neg v)
                     (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                           (klcx_epos (real_abs (real_plus u (real_opp v)))))
                                eps)).
Proof.
  intros u v eps Heps.
  apply (real_le_eq_r _
           (real_mult (real_exp_neg v)
                      (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                            (cauchy_real_exp (real_abs (real_plus u (real_opp v)))))
                                 eps))).
  - exact (real_exp_neg_diff_bound u v eps Heps).
  - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)).
    apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
               (real_eq_sym _ _ (klcx_epos_correct _))).
    + apply real_eq_refl.
Qed.

(* 接口语形投影出口（@le/@lt = RealEnhancedReal 字段，与 real_le/   *)
(* real_lt 同体——槽位 Or 形 le 的 Real 实例语形版） *)
Theorem klcx_boltzmann_diff_bridge_iface : forall (u v eps : Real),
  @lt Real RealEnhancedReal real_zero eps ->
  @le Real RealEnhancedReal
     (real_abs (real_plus (real_exp_neg u) (real_opp (real_exp_neg v))))
     (real_mult (real_exp_neg v)
                (real_plus (real_mult (real_abs (real_plus u (real_opp v)))
                                      (klcx_epos (real_abs (real_plus u (real_opp v)))))
                           eps)).
Proof.
  exact (fun u v eps => klcx_boltzmann_diff_bridge u v eps).
Qed.

(* ============================================================ *)
(* K-C 放电件 2：exp_neg_geo_break（UpReqAttnGibbs:2146）            *)
(*   槽形：d>0 ⟹ ∃N, e^{−2^N·d} ≤ eps（req_r_pow(1+1) N → 载体      *)
(*   klcx_r_pow 镜像 req_r_pow 逐位定义）。                          *)
(*   证书链：root exp_lower_q（e^{−N₀}<eps，N₀≥2）+ real_arch        *)
(*   （N₀/d < m#1）+ 2^m>m（nat+real_const_lt）+ exp 单调。          *)
(* ============================================================ *)

(* 载体：镜像 req_r_pow（1 / x·x^k 逐位），Real 层 *)
Fixpoint klcx_r_pow (x : Real) (n : nat) : Real :=
  match n with
  | Datatypes.O => real_one
  | Datatypes.S k => real_mult x (klcx_r_pow x k)
  end.

Lemma klcx_nat_lt_two_pow : forall n : nat,
  Qlt (Z.of_nat n # 1) (Z.of_nat (Nat.pow 2 n) # 1).
Proof.
  intro n.
  assert (Hnat : (n < Nat.pow 2 n)%nat) by (induction n; simpl; lia).
  assert (Hz : (Z.of_nat n < Z.of_nat (Nat.pow 2 n))%Z)
    by (apply Nat2Z.inj_lt; exact Hnat).
  unfold Qlt. cbn [Qnum Qden]. rewrite !Zmult_1_r. exact Hz.
Qed.

Lemma klcx_const_rpow_eq : forall n : nat,
  real_eq (real_const (Z.of_nat (Nat.pow 2 n) # 1))
          (klcx_r_pow (real_plus real_one real_one) n).
Proof.
  induction n as [| k IH].
  - simpl. exact klcx_const_one_eq.
  - change (Nat.pow 2 (Datatypes.S k)) with (2 * Nat.pow 2 k)%nat.
    rewrite (Nat2Z.inj_mul 2 (Nat.pow 2 k)).
    apply (real_eq_trans _
             (real_mult (real_const (2 # 1))
                        (real_const (Z.of_nat (Nat.pow 2 k) # 1)))).
    + apply real_eq_sym. apply b5j_real_const_mult_eq.
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _
               klcx_const_two_eq IH).
Qed.

Lemma klcx_exp_neg_opp_const_eq : forall n : nat,
  real_eq (cauchy_real_exp (real_opp (real_const (Z.of_nat n # 1))))
          (cauchy_real_exp (real_const (Qopp (Z.of_nat n # 1)))).
Proof.
  intro n. apply cauchy_real_exp_wd. apply real_eq_of_zero_diff.
  intro m.
  assert (Hp : projT1 (real_const (Qopp (Z.of_nat n # 1))) m
               == Qopp (Z.of_nat n # 1))
    by (apply (real_const_proj (Qopp (Z.of_nat n # 1)) m)).
  assert (Hq0 : projT1 (real_const (Z.of_nat n # 1)) m == Z.of_nat n # 1)
    by (apply (real_const_proj (Z.of_nat n # 1) m)).
  assert (Hq : projT1 (real_opp (real_const (Z.of_nat n # 1))) m
               == Qopp (Z.of_nat n # 1)).
  { rewrite (real_opp_proj (real_const (Z.of_nat n # 1)) m).
    apply (Qopp_comp _ _ Hq0). }
  rewrite Hp. rewrite Hq. unfold Qminus. ring.
Qed.

Theorem klcx_exp_neg_geo_break : forall (d eps : Real),
  real_lt real_zero d -> real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_le (real_exp_neg
               (real_mult (klcx_r_pow (real_plus real_one real_one) N) d))
            eps).
Proof.
  intros d eps Hd Heps.
  destruct (exp_lower_q eps Heps) as [N0 [HN02 Hlt0]].
  set (N0R := real_const (Z.of_nat N0 # 1)).
  destruct (real_arch (real_mult N0R (real_inv_pos d Hd)))
    as [m [Hm2 Harch]].
  set (mR := real_const (Z.of_nat m # 1)).
  (* m > N₀/d ⟹ N₀ < m·d（正 d 右乘 + inv 吸收） *)
  assert (Hstep : real_lt (real_mult (real_mult N0R (real_inv_pos d Hd)) d)
                          (real_mult mR d))
    by (apply (klcx_lt_mult_r _ _ d Hd Harch)).
  assert (Heq : real_eq (real_mult (real_mult N0R (real_inv_pos d Hd)) d) N0R).
  { apply (real_eq_trans _
             (real_mult N0R (real_mult (real_inv_pos d Hd) d))).
    - apply real_eq_sym. apply real_mult_assoc.
    - apply (real_eq_trans _
               (real_mult N0R real_one)).
      + apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)).
        apply (real_eq_trans (real_mult (real_inv_pos d Hd) d)
                             (real_mult d (real_inv_pos d Hd))).
        * apply real_mult_comm.
        * exact (real_inv_pos_correct d Hd).
      + apply real_mult_one. }
  assert (Hlt1 : real_lt N0R (real_mult mR d))
    by (exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ Heq) Hstep)).
  (* m#1 < 2^m（Q 层 nat 事实 + real_const_lt + 载体换形） *)
  assert (Hlt2 : real_lt mR (klcx_r_pow (real_plus real_one real_one) m)).
  { apply (real_lt_eq_lt _ (real_const (Z.of_nat (Nat.pow 2 m) # 1)) _).
    - exact (real_const_lt _ _ (klcx_nat_lt_two_pow m)).
    - exact (klcx_const_rpow_eq m). }
  assert (Hlt3 : real_lt (real_mult mR d)
                         (real_mult (klcx_r_pow (real_plus real_one real_one) m) d))
    by (apply (klcx_lt_mult_r _ _ d Hd Hlt2)).
  assert (Hlt4 : real_lt N0R
                   (real_mult (klcx_r_pow (real_plus real_one real_one) m) d))
    by (exact (real_lt_trans _ _ _ Hlt1 Hlt3)).
  (* 反向 + exp 单调 + Qopp 常数换形 + exp_lower_q 收口 *)
  assert (Hlt5 : real_lt
                   (real_opp (real_mult (klcx_r_pow (real_plus real_one real_one) m) d))
                   (real_opp N0R))
    by (apply (real_opp_lt_compat _ _ Hlt4)).
  assert (Hlt6 : real_lt (cauchy_real_exp
                            (real_opp (real_mult (klcx_r_pow (real_plus real_one real_one) m) d)))
                         (cauchy_real_exp (real_opp N0R)))
    by (apply (cauchy_real_exp_mono _ _ Hlt5)).
  assert (Hlt7 : real_lt (cauchy_real_exp
                            (real_opp (real_mult (klcx_r_pow (real_plus real_one real_one) m) d)))
                         (cauchy_real_exp (real_const (Qopp (Z.of_nat N0 # 1)))))
    by (exact (real_lt_eq_lt _ _ _ Hlt6 (klcx_exp_neg_opp_const_eq N0))).
  exists m. exact (inl (real_lt_trans _ _ _ Hlt7 Hlt0)).
Qed.

(* 接口语形投影出口（sigT + @le，槽语句的 Real 实例语形版） *)
Theorem klcx_exp_neg_geo_break_iface : forall (d eps : Real),
  @lt Real RealEnhancedReal real_zero d ->
  @lt Real RealEnhancedReal real_zero eps ->
  sigT (fun N : nat =>
    @le Real RealEnhancedReal
        (real_exp_neg
           (real_mult (klcx_r_pow (real_plus real_one real_one) N) d))
        eps).
Proof.
  exact (fun d eps => klcx_exp_neg_geo_break d eps).
Qed.

(* ============================================================ *)
(* K-D 放电件 3：r_arch_pow（UpReqCauchy:221）+ arch_pow_i           *)
(*   （UpReqAttnIter:163）统一件 + 两槽镜像实例                      *)
(*   证书链 = CW220_Extensions.BudgetReal.r_arch_pow_real（在盘      *)
(*   件：real_arch + Bernoulli + 逆元链，其 .vo 同轨四关绿）一次      *)
(*   喂定；klcx_r_pow 与 BudgetReal.real_pow 逐位同 Fixpoint 体       *)
(*   （delta 透明，klcx_r_pow_pow_eq 显式登记）。                     *)
(* ============================================================ *)

Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.

(* 载体透明登记：klcx_r_pow x n ≡ real_pow x n（同一递归体） *)
Lemma klcx_r_pow_pow_eq : forall (x : Real) (n : nat),
  real_eq (klcx_r_pow x n) (real_pow x n).
Proof.
  intros x n. exact (real_eq_refl (klcx_r_pow x n)).
Qed.

(* 统一件：几何击穿阿基米德（0<k<1 ⟹ ∃N, a·k^N < eps）——
   r_arch_pow 槽（UpReqCauchy:221 Variable 位）与 arch_pow_i 槽
   （UpReqAttnIter:163 Variable 位，底 k := 1−δ）的同形核 *)
Theorem klcx_geo_pow_break : forall (k a eps : Real),
  real_lt real_zero k -> real_lt k real_one ->
  real_lt real_zero a -> real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a (klcx_r_pow k N)) eps).
Proof.
  intros k a eps Hk1 Hk2 Ha Heps.
  exact (r_arch_pow_real k Hk1 Hk2 a Ha eps Heps).
Qed.

(* 槽镜像 1：r_arch_pow（UpReqCauchy:221）接口语形投影出口
   （k 对应节变量 kappa，0<k<1 前提位随槽显式参） *)
Theorem klcx_r_arch_pow_iface : forall (k a eps : Real),
  @lt Real RealEnhancedReal real_zero k ->
  @lt Real RealEnhancedReal k real_one ->
  @lt Real RealEnhancedReal real_zero a ->
  @lt Real RealEnhancedReal real_zero eps ->
  sigT (fun n : nat =>
    @lt Real RealEnhancedReal (real_mult a (klcx_r_pow k n)) eps).
Proof.
  exact (fun k a eps => klcx_geo_pow_break k a eps).
Qed.

(* 槽镜像 2：arch_pow_i（UpReqAttnIter:163）接口语形投影出口
   （底 := 1−δ；0<δ 与 δ<1 两前提位对应节内 omd 正性条件） *)
Theorem klcx_arch_pow_omd_iface : forall (delta a eps : Real),
  @lt Real RealEnhancedReal real_zero delta ->
  @lt Real RealEnhancedReal delta real_one ->
  @lt Real RealEnhancedReal real_zero a ->
  @lt Real RealEnhancedReal real_zero eps ->
  sigT (fun N : nat =>
    @lt Real RealEnhancedReal
        (real_mult a (klcx_r_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta a eps Hd1 Hd2 Ha Heps.
  apply (klcx_geo_pow_break (real_plus real_one (real_opp delta)) a eps).
  - exact (one_minus_delta_pos_real delta Hd2).
  - exact (one_minus_delta_lt_one_real delta Hd1).
  - exact Ha.
  - exact Heps.
Qed.

Print Assumptions klcx_boltzmann_diff_bridge.
Print Assumptions klcx_exp_neg_geo_break.
Print Assumptions klcx_geo_pow_break.
Print Assumptions klcx_r_arch_pow_iface.
Print Assumptions klcx_arch_pow_omd_iface.
