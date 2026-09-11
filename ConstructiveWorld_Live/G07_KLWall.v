(* G 组：G07_KLWall — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpReqKLCvx + UpReqPowB + UpReqJensen + UpReqKLStrict + UpReqKLEnergy（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G07_KLWall 成员件：UpReqKLCvx（原样并入，自带 Require）======== *)
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

(* ======== G07_KLWall 成员件：UpReqPowB（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqPowB.v —— 幂运算 le_b/Bishop 序构造席（广义旗舰链·定理 4.8      *)
(*   Bishop 形两大承重墙之一：幂律骨架）                              *)
(*                                                              *)
(* 主结果（全部 Set 层、零 Prop 泄露、零新公理、单调性零 Or 分支）：      *)
(*   0. powb_pow：nat 指数幂载体（Real 层 Fixpoint，O ↦ one，          *)
(*      S m ↦ mult base (powb_pow base m)；CW220 real_pow 同形独立      *)
(*      复刻，零上游改动）。                                           *)
(*   1. powb_le_b_refl：≤_B 自反退化件（real_lt_plus_r_zero 项式直给）。 *)
(*   2. powb_pos_lt：正底幂严格正（归纳 + real_mult_positive 引擎件）。  *)
(*   3. powb_pos（保底件2）：正底幂 Bishop 形恒正 0 ≤_B base^t          *)
(*      （逐 eps：严格正 + plus_r_zero 传递，一步收口）。               *)
(*   4. powb_sub_one（主件2）：0 < base ≤ 1 ⟹ base^{S n} ≤_B base^n     *)
(*      （每步不增；见证 e₀ := eps·inv(base^n)，base ≤_B 1（单向桥      *)
(*      换形）取 e₀ 后乘正因子 base^n：(1+e₀)·u == u+eps 换形收口；      *)
(*      lt 支 real_mult_lt_compat 右乘正因子、eq 支换形 + 平凡平移；      *)
(*      证明体零 Or 分支——单调性不走精确比较）。                        *)
(*   5. powb_le_one_pow（主件）：0 < base ≤ 1 ∧ t:nat ⟹ base^t ≤_B 1   *)
(*      （幂不超一；归纳 + sub_one + ≤_B 传递组合器链式收口）。          *)
(*   6. powb_mono_dec（保底件）：NatLe n m ∧ 0 < base ≤ 1 ⟹             *)
(*      base^m ≤_B base^n（幂单调递减 Bishop 形；序界取 Set 层 NatLe     *)
(*      （基座 Id(leb) 编码，全库先例）；归纳直证——le 推导链上每步       *)
(*      sub_one + real_le_b_trans（eps 半分组合器）传递，零 Or 分支、     *)
(*      零精确比较）。                                                  *)
(*   7. 旗舰（定理 4.8 幂律直接入口）：(1−η)^t 的 Bishop 形——            *)
(*      powb_one_minus_eta_pos：0<η<1 ⟹ 0<1−η（平移+opp 换形）；         *)
(*      powb_one_minus_eta_base_le_one：0<η ⟹ 1−η ≤ 1（加 η 换形=1）；   *)
(*      powb_one_minus_eta_le_one：(1−η)^t ≤_B 1；                       *)
(*      powb_one_minus_eta_mono_dec：NatLe t t1 ⟹ (1−η)^{t1} ≤_B        *)
(*      (1−η)^t——几何收缩幂律全量入口。                                 *)
(*   诚实边界判词：闭区间上端 η=1 时 1−η 的严格正性证书构造性不可分      *)
(*   （1−η==0 与 1−η>0 不可分），闭端版本须另设零退化分支——挂账未建；    *)
(*   开区间 (0,1) 版已覆盖定理 4.8 收缩入口（η 为收缩率恒 <1）。         *)
(*                                                              *)
(* 引擎消费：UpRealLeB（real_le_b/单向桥 real_le_to_le_b/lt 平移底座     *)
(* real_lt_plus_r_zero）＋ UpRealLeB2（real_le_b_trans ≤_B 传递组合器，  *)
(* eps 半分）。基底 CW_ConstructiveWorld_219（Real 层代数与序引擎件）。  *)
(* 红线：零公理零未闭合证明（G1 禁词全零）；全语句 Set 层（序界 NatLe、   *)
(* real_le_b、real_lt/real_le 全 Set 值，零 sigT 见证形语句）；既有文件   *)
(* 零改；纯 term-mode 显式组装（real_eq 非 Id，禁 rewrite，全链          *)
(* real_eq_trans/compat）；全 Qed. 闭合；新件 Print Assumptions 全       *)
(* Closed（文末十条）。                                                 *)
(* 编译配方：coqc 9.0（与树内 .vo magic 90001 同轨，UpRealLeB2 先例）    *)
(*   coqc -Q . "" -Q "..\001" "" UpReqPowB.v（cpu_guard 包装零裸调）     *)
(* ============================================================ *)

From Stdlib Require Import PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 0. 载体 + 退化件                                                   *)
(* ============================================================ *)

(* nat 指数幂（Real 层 Fixpoint；与 CW220 real_pow 同形、独立命名防撞） *)
Fixpoint powb_pow (base : Real) (t : nat) : Real :=
  match t with
  | O => real_one
  | Datatypes.S m => real_mult base (powb_pow base m)
  end.

(* ≤_B 自反（one 收口器退化形；real_lt_plus_r_zero 项式直给） *)
Lemma powb_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intros x. unfold real_le_b. intros eps Heps.
  exact (real_lt_plus_r_zero x eps Heps).
Qed.

(* ============================================================ *)
(* 1. 严格正性归纳 + 保底件2 powb_pos                                  *)
(* ============================================================ *)

(* 正底幂严格正（归纳；乘法正性引擎件 real_mult_positive） *)
Lemma powb_pos_lt : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_lt real_zero (powb_pow base t).
Proof.
  intros base t Hb. induction t as [| m IH].
  - exact real_lt_zero_one.
  - cbn [powb_pow].
    exact (real_mult_positive base (powb_pow base m) Hb IH).
Qed.

(* 保底件2：正底幂 Bishop 形恒正 0 ≤_B base^t（逐 eps 收口） *)
Lemma powb_pos : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le_b real_zero (powb_pow base t).
Proof.
  intros base t Hb. unfold real_le_b. intros eps Heps.
  apply (real_lt_trans real_zero (powb_pow base t)
           (real_plus (powb_pow base t) eps)).
  - exact (powb_pos_lt base t Hb).
  - exact (real_lt_plus_r_zero (powb_pow base t) eps Heps).
Qed.

(* ============================================================ *)
(* 2. 主件2 powb_sub_one：base^{S n} ≤_B base^n（每步不增）             *)
(* ============================================================ *)

Lemma powb_sub_one : forall (base : Real) (n : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base (Datatypes.S n)) (powb_pow base n).
Proof.
  intros base n Hb Hle.
  pose proof (real_le_to_le_b base real_one Hle) as Hleb.
  pose proof (powb_pos_lt base n Hb) as Hu.
  pose proof (real_inv_pos_pos (powb_pow base n) Hu) as Hinv.
  unfold real_le_b. intros eps Heps. cbn [powb_pow].
  pose proof (real_mult_positive eps (real_inv_pos (powb_pow base n) Hu)
                Heps Hinv) as He0.
  (* 换形底座：(1 + e₀)·u == u + eps（e₀ := eps·inv u） *)
  assert (Hshape : real_eq
    (real_mult (real_plus real_one
                  (real_mult eps (real_inv_pos (powb_pow base n) Hu)))
               (powb_pow base n))
    (real_plus (powb_pow base n) eps)).
  { apply (real_eq_trans _
             (real_mult (powb_pow base n)
                (real_plus real_one
                   (real_mult eps (real_inv_pos (powb_pow base n) Hu)))) _).
    - apply real_mult_comm.
    - apply (real_eq_trans _
               (real_plus (real_mult (powb_pow base n) real_one)
                          (real_mult (powb_pow base n)
                             (real_mult eps
                                (real_inv_pos (powb_pow base n) Hu)))) _).
      + apply real_distrib.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (powb_pow base n) real_one)
                 (real_mult (powb_pow base n)
                    (real_mult eps (real_inv_pos (powb_pow base n) Hu)))
                 (powb_pow base n)
                 eps).
        * apply real_mult_one.
        * (* u·(eps·inv u) == eps *)
          apply (real_eq_trans _
                     (real_mult
                        (real_mult eps (real_inv_pos (powb_pow base n) Hu))
                        (powb_pow base n)) _).
          -- apply real_mult_comm.
          -- apply (real_eq_trans _
                       (real_mult eps
                          (real_mult (real_inv_pos (powb_pow base n) Hu)
                                     (powb_pow base n))) _).
             ++ apply real_eq_sym. apply real_mult_assoc.
             ++ apply (real_eq_trans _ (real_mult eps real_one) _).
                ** apply (RealSetoid.real_eq_mult_compat eps
                             (real_mult (real_inv_pos (powb_pow base n) Hu)
                                        (powb_pow base n))
                             eps real_one).
                   { apply real_eq_refl. }
                   { apply (real_eq_trans _
                                (real_mult (powb_pow base n)
                                   (real_inv_pos (powb_pow base n) Hu)) _).
                     - apply real_mult_comm.
                     - apply real_inv_pos_correct. }
                ** apply real_mult_one. }
  (* base ≤_B 1 取 e₀：直接得严格界 base < 1+e₀（le_b 结果为 real_lt
     见证形，单支收口，零 Or 分支） *)
  pose proof (Hleb (real_mult eps (real_inv_pos (powb_pow base n) Hu)) He0)
    as Hlt.
  apply (RealSetoid.real_lt_id_r
             (real_mult base (powb_pow base n))
             (real_mult (real_plus real_one
                           (real_mult eps
                              (real_inv_pos (powb_pow base n) Hu)))
                        (powb_pow base n))
             (real_plus (powb_pow base n) eps)).
  - exact Hshape.
  - exact (real_mult_lt_compat base
               (real_plus real_one
                  (real_mult eps (real_inv_pos (powb_pow base n) Hu)))
               (powb_pow base n) Hlt Hu).
Qed.

(* ============================================================ *)
(* 3. 主件 powb_le_one_pow：base^t ≤_B 1（幂不超一）                    *)
(* ============================================================ *)

Lemma powb_le_one_pow : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (powb_pow base t) real_one.
Proof.
  intros base t Hb Hle. induction t as [| m IH].
  - exact (powb_le_b_refl real_one).
  - apply (real_le_b_trans (powb_pow base (Datatypes.S m))
             (powb_pow base m) real_one).
    + exact (powb_sub_one base m Hb Hle).
    + exact IH.
Qed.

(* ============================================================ *)
(* 4. 保底件 powb_mono_dec：base^m ≤_B base^n（幂单调递减，Set 层序界）  *)
(*    （序界取 Set 层 NatLe（基座 Id(leb) 编码，全库先例）；归纳直证——   *)
(*      m 归纳 + n 分情形 + 单布尔分叉（leb (S n1) m），Prop 侧只经      *)
(*      Nat.leb_le/lift、leb_gt/antisymm 做等词回填，零 Or 消去入 Set、  *)
(*      零精确比较；单调链全程 sub_one + real_le_b_trans 传递。）        *)
(* ============================================================ *)

Lemma powb_mono_dec : forall (base : Real) (m : nat),
  real_lt real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (powb_pow base m) (powb_pow base n).
Proof.
  intros base m Hb Hle. induction m as [| m IH]; intros n Hnm.
  - destruct n as [| n1].
    + exact (powb_le_b_refl (powb_pow base 0)).
    + (* NatLe (S n1) 0 即 Id false true，零案例爆破 *)
      destruct (id_false_true Hnm).
  - destruct n as [| n1].
    + exact (powb_le_one_pow base (Datatypes.S m) Hb Hle).
    + destruct (Nat.leb (Datatypes.S n1) m) eqn:E2.
      * (* S n1 ≤ m：sub_one + IH 传递链 *)
        apply (real_le_b_trans (powb_pow base (Datatypes.S m))
                 (powb_pow base m) (powb_pow base (Datatypes.S n1))).
        -- exact (powb_sub_one base m Hb Hle).
        -- apply IH.
           apply (NatLe_lift (Datatypes.S n1) m).
           apply (proj1 (Nat.leb_le (Datatypes.S n1) m)). exact E2.
      * (* ¬(S n1 ≤ m) ∧ n1 ≤ m ⟹ n1 = m：反对称回填后自反 *)
        pose proof (proj1 (Nat.leb_gt (Datatypes.S n1) m) E2) as Hgt.
        pose proof (NatLe_drop n1 m Hnm) as Hn1m.
        pose proof (Nat.le_antisymm n1 m Hn1m
                     (proj1 (Nat.lt_succ_r m n1) Hgt)) as Heq.
        rewrite Heq.
        exact (powb_le_b_refl (powb_pow base (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* 5. 旗舰：(1−η)^t 的 Bishop 形（定理 4.8 幂律直接入口）               *)
(*    （1−η 以 real_plus real_one (real_opp eta) 字面承载，与根层        *)
(*      real_pow_pos 消费面同形）                                      *)
(* ============================================================ *)

(* 1−η 严格正（0<η<1：平移 + opp 换形，零分支） *)
Lemma powb_one_minus_eta_pos : forall eta : Real,
  real_lt real_zero eta -> real_lt eta real_one ->
  real_lt real_zero (real_plus real_one (real_opp eta)).
Proof.
  intros eta Hpos Hlt.
  pose proof (real_lt_plus_translate (real_opp eta) eta real_one Hlt) as Htr.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus (real_opp eta) eta)
           (real_plus real_one (real_opp eta))).
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_plus eta (real_opp eta)) _).
    + apply real_plus_comm.
    + apply real_plus_opp.
  - apply (RealSetoid.real_lt_id_r
             (real_plus (real_opp eta) eta)
             (real_plus (real_opp eta) real_one)
             (real_plus real_one (real_opp eta))).
    + apply real_plus_comm.
    + exact Htr.
Qed.

(* 1−η ≤ 1（0<η：(1−η)+η 换形 =1；零分支） *)
Lemma powb_one_minus_eta_base_le_one : forall eta : Real,
  real_lt real_zero eta ->
  real_le (real_plus real_one (real_opp eta)) real_one.
Proof.
  intros eta Hpos.
  assert (Heqsum : real_eq
    (real_plus (real_plus real_one (real_opp eta)) eta) real_one).
  { apply (real_eq_trans _
             (real_plus real_one (real_plus (real_opp eta) eta)) _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (real_eq_trans _
               (real_plus real_one (real_plus eta (real_opp eta))) _).
      + apply (RealSetoid.real_eq_plus_compat real_one
                 (real_plus (real_opp eta) eta) real_one
                 (real_plus eta (real_opp eta))).
        * apply real_eq_refl.
        * apply real_plus_comm.
      + apply (real_eq_trans _ (real_plus real_one real_zero) _).
        * apply (RealSetoid.real_eq_plus_compat real_one
                   (real_plus eta (real_opp eta)) real_one real_zero).
          -- apply real_eq_refl.
          -- apply real_plus_opp.
        * apply real_plus_zero. }
  pose proof (real_lt_plus_r_zero (real_plus real_one (real_opp eta)) eta
                Hpos) as Hlt0.
  pose proof (real_lt_eq_lt
    (real_plus real_one (real_opp eta))
    (real_plus (real_plus real_one (real_opp eta)) eta)
    real_one Hlt0 Heqsum) as Hlt1.
  exact (RealSetoid.real_lt_le_iff_req (real_plus real_one (real_opp eta))
           real_one (inl Hlt1)).
Qed.

(* 旗舰上界：(1−η)^t ≤_B 1 *)
Lemma powb_one_minus_eta_le_one : forall (eta : Real) (t : nat),
  real_lt real_zero eta -> real_lt eta real_one ->
  real_le_b (powb_pow (real_plus real_one (real_opp eta)) t) real_one.
Proof.
  intros eta t Hpos Hlt.
  apply (powb_le_one_pow (real_plus real_one (real_opp eta)) t).
  - exact (powb_one_minus_eta_pos eta Hpos Hlt).
  - exact (powb_one_minus_eta_base_le_one eta Hpos).
Qed.

(* 旗舰单调：(1−η)^{t1} ≤_B (1−η)^t（t ≤ t1；几何收缩幂律） *)
Theorem powb_one_minus_eta_mono_dec : forall (eta : Real) (t t1 : nat),
  real_lt real_zero eta -> real_lt eta real_one -> NatLe t t1 ->
  real_le_b (powb_pow (real_plus real_one (real_opp eta)) t1)
            (powb_pow (real_plus real_one (real_opp eta)) t).
Proof.
  intros eta t t1 Hpos Hlt Hle.
  apply (powb_mono_dec (real_plus real_one (real_opp eta)) t1
           (powb_one_minus_eta_pos eta Hpos Hlt)
           (powb_one_minus_eta_base_le_one eta Hpos) t Hle).
Qed.

(* ============================================================ *)
(* 尾注：诚实台账（判词供论文侧与四关报告引用）                          *)
(* 【判词 P1｜载体】powb_pow 与 CW220 real_pow 同形独立复刻——零上游      *)
(*   依赖（仅 Require 根层 + LeB 引擎两库），消费者可按需与 real_pow     *)
(*   换形对接（eq_compat 级对接件挂账未建，非本席红线内）。              *)
(* 【判词 P2｜单调性零 Or 分支】powb_mono_dec 归纳直证成立——序界取      *)
(*   NatLe（Set 层 Id(leb) 编码）后，le 推导链每步 sub_one + ≤_B 传递    *)
(*   组合器链式收口；全链无 real_le 前提位 Or 分支、无精确比较。          *)
(* 【判词 P3｜sub_one 见证形】e₀ := eps·inv(base^n)：Bishop 乘法收口     *)
(*   标准形（UpRealLeB 收口引理 e₀ := eps'·inv(2D) 同族）；lt/eq 两支    *)
(*   分别右乘正因子保序 / 等式换形+平凡平移闭合。                        *)
(* 【判词 P4｜闭端挂账】η=1 时 1−η 严格正性证书构造性不可分（1−η==0 与   *)
(*   1−η>0 不可分），闭区间 (0,1] 版须零退化分支另设路径——挂账未建；      *)
(*   开区间 (0,1) 版为定理 4.8 收缩率场景的正配入口。                    *)
(* 【机器状态】四关卡证据：G1 禁词全零；G2 EXIT=0 + 十件 Print           *)
(*   Assumptions Closed；G3 提取探针 Obj.magic=0；G4 coqchk 通过         *)
(*   （log 见 _powb_* 序列）。                                          *)
(* ============================================================ *)

Print Assumptions powb_le_b_refl.
Print Assumptions powb_pos_lt.
Print Assumptions powb_pos.
Print Assumptions powb_sub_one.
Print Assumptions powb_le_one_pow.
Print Assumptions powb_mono_dec.
Print Assumptions powb_one_minus_eta_pos.
Print Assumptions powb_one_minus_eta_base_le_one.
Print Assumptions powb_one_minus_eta_le_one.
Print Assumptions powb_one_minus_eta_mono_dec.

(* ======== G07_KLWall 成员件：UpReqJensen（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqJensen.v —— 定理 4.8 承重墙席：log-sum-exp 凸性 Bishop 形    *)
(*   （jens_ 前缀；广义旗舰链·le_b 证明席）                         *)
(*                                                                *)
(* 数学目标（构造性，le_b/eps 语言，Set 层零 Prop）：               *)
(*   ① jens_exp_tangent：1 − x ≤ exp(−x)（逐 eps + le_b 双形）      *)
(*      ——切线下界，exp 凸性的种子（CW219 real_exp_ge_linear_eps    *)
(*      在 t := −x 的特化 + Bishop 收口）。                          *)
(*   ② jens_two_point：exp((1−η)x+ηy) ≤ (1−η)exp x + η exp y       *)
(*      （逐 eps + le_b 双形；η 形主件 + w 形伴生件）。              *)
(*   ③ jens_weighted_n_point（主件）：加权 n 点 Jensen              *)
(*      exp(Σ w_i·x_i) ≤_B Σ w_i·exp(x_i)                           *)
(*      （w_i ≥ 0、Σw_i == 1；任意指标型 list X）。                  *)
(*      路线 = 切线锥逐点化（Varberg 锥免除法形态）：                *)
(*        exp(x_i) ≥ exp(z)·(1 + x_i − z)（z := Σw_i x_i 处切线）    *)
(*        逐点乘非负系数 E·w_i（E := exp z > 0 证书既有实测）        *)
(*        求和 + 归一化坍缩 Σ w_i·(1+x_i−z) == 1                    *)
(*        ⟹ Σ w_i·exp(x_i) ≥ exp(z)·1 == exp(z)。                   *)
(*      误差吸收走 real_le_closure_b（D := E > 0 收口器），          *)
(*      零除法、零折半、零三分律。                                   *)
(*   ④ jens_partition（旗舰）：Z = Σ π_t^{1−η}·π*^η ≤_B 1           *)
(*      （逐点 AM-GM + 误差配权 eps·π_t 归一化吸收；                 *)
(*        CW219 real_interp_Z_le_one_eps 的任意指标型泛化            *)
(*        （nat-seq → list X）+ le_b 收口——                          *)
(*        定理 4.8 step_kl_eta_bound 的数学核）。                    *)
(*                                                                *)
(* ---------------------------------------------------------------- *)
(* 勘误④（方向修正，沿 CW220 M0.1 先例入档）：                      *)
(*   任务书原式「Σ w_i·exp(−x_i) ≤ exp(−Σ w_i·x_i) + eps」方向反了： *)
(*   exp 为凸，Jensen 给 exp(加权平均) ≤ 加权和（反向一般假；        *)
(*   数值反例 w=(1/2,1/2)、x=(−1,1)：LHS≈1.543 > 1 = RHS）。          *)
(*   本席按真值方向陈述：exp(Σ w_i x_i) ≤ Σ w_i exp(x_i) + eps      *)
(*   （等价负参形 exp(−Σw x) ≤ Σ w exp(−x) + eps）。                 *)
(*   该方向恰为 Hölder/插值 Z ≤ (Σπ)^{1−η}(Σπ* )^η = 1 的可行路径   *)
(*   （逐点凸性 + 归一化求和），与旗舰④一致——勘误后目标不变。       *)
(*   另：侦察注记——CW219 的 exp 全参数可用（real_exp_ge_linear_eps  *)
(*   三分支覆盖全 t），接口记录的 exp_neg 命名系字段名而非限制；      *)
(*   本席所有语句直接用 cauchy_real_exp 任意实参，零符号翻转负担。   *)
(*                                                                *)
(* 侦察结论（全部 sed/grep 实读）：                                  *)
(*   种子：real_exp_ge_linear_eps@CW219:40962（1+t ≤ exp t + eps，    *)
(*   逐 eps 构造）；两点核：real_exp_two_point_cvx_eps@CW219:112669  *)
(*   （Varberg 锥）；AM-GM：real_amgm_pointwise_eps@CW219:112817；    *)
(*   求和引擎：real_list_sum 五件@CW219:41491-41666（ext/add/        *)
(*   linear/linear_r/le）；收口器：real_le_closure_b@UpRealLeB       *)
(*   + closure_b_one@UpRealLeB:373 + 非负系数器@UpRealLeB2:102；     *)
(*   换形面：real_opp_le_compat/real_opp_opp/real_distrib/           *)
(*   cauchy_real_exp_plus@34782/cauchy_real_exp_wd@35117/            *)
(*   cauchy_real_exp_pos@13376 区。                                  *)
(*   缺位核实：jensen/加权 n 点 exp 不等式全库零命中——主件为真增量；  *)
(*   jens_ 前缀全库零占用（建前 grep 实测）。                         *)
(*                                                                *)
(* 红线：零公理零未闭合证明（G1 禁词全零）；Set 层语句（real_le_b    *)
(*   为 Set 值 forall 型，结论零 Prop 泄露）；全 Qed. 闭合；         *)
(*   既有文件零改；零 git。                                          *)
(* 编译配方：coqc -Q . "" -Q "..\001" "" UpReqJensen.v               *)
(*   （cpu_guard.ps1 温控包装，绑核错峰，零裸调）。                  *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part A：环换形底座（real_eq 链件，纯 term-mode 组装）             *)
(* ============================================================ *)

(* A.1：z + (x + (−z)) == x（切线锥坍缩的核恒等式） *)
Lemma jens_ring_z_cancel : forall z x : Real,
  real_eq (real_plus z (real_plus x (real_opp z))) x.
Proof.
  intros z x.
  apply (real_eq_trans _ (real_plus z (real_plus (real_opp z) x)) _).
  - apply (RealSetoid.real_eq_plus_compat z (real_plus x (real_opp z))
             z (real_plus (real_opp z) x)).
    + apply real_eq_refl.
    + apply real_plus_comm.
  - apply (real_eq_trans _ (real_plus (real_plus z (real_opp z)) x) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_plus real_zero x) _).
      * apply (RealSetoid.real_eq_plus_compat (real_plus z (real_opp z)) x
                 real_zero x).
        -- apply real_plus_opp.
        -- apply real_eq_refl.
      * apply sf_real_plus_zero_l.
Qed.

(* A.2：1 − (1 − w) == w（w 形两点件的方向换形核） *)
Lemma jens_ring_one_involut : forall w : Real,
  real_eq (real_plus real_one (real_opp (real_plus real_one (real_opp w)))) w.
Proof.
  intro w.
  apply (real_eq_trans _
           (real_plus real_one
              (real_plus (real_opp real_one) (real_opp (real_opp w)))) _).
  - apply (RealSetoid.real_eq_plus_compat real_one
             (real_opp (real_plus real_one (real_opp w))) real_one
             (real_plus (real_opp real_one) (real_opp (real_opp w)))).
    + apply real_eq_refl.
    + apply real_opp_plus.
  - apply (real_eq_trans _
             (real_plus (real_plus real_one (real_opp real_one))
                        (real_opp (real_opp w))) _).
    + apply real_plus_assoc.
    + apply (real_eq_trans _ (real_opp (real_opp w)) _).
      * apply (real_eq_trans _
                 (real_plus real_zero (real_opp (real_opp w))) _).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_plus real_one (real_opp real_one))
                     (real_opp (real_opp w)) real_zero (real_opp (real_opp w))).
           ++ apply real_plus_opp.
           ++ apply real_eq_refl.
        -- apply sf_real_plus_zero_l.
      * apply real_opp_opp.
Qed.

(* ============================================================ *)
(* Part B：保底件2 —— jens_exp_tangent（切线下界，双形）             *)
(*   1 − x ≤ exp(−x) + eps（逐 eps）；le_b 形经 one 特化收口。       *)
(* ============================================================ *)

Lemma jens_exp_tangent_eps : forall (x eps : Real),
  real_lt real_zero eps ->
  real_le (real_plus real_one (real_opp x))
          (real_plus (cauchy_real_exp (real_opp x)) eps).
Proof.
  intros x eps Heps.
  exact (RealInterfaceEnhancedMod.real_exp_ge_linear_eps (real_opp x) eps Heps).
Qed.

Lemma jens_exp_tangent : forall x : Real,
  real_le_b (real_plus real_one (real_opp x))
            (cauchy_real_exp (real_opp x)).
Proof.
  intro x.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (jens_exp_tangent_eps x eps Heps).
Qed.

(* ============================================================ *)
(* Part C：保底件 —— jens_two_point（两点凸性，双形 + 双参数形）      *)
(*   真值方向（勘误④）：exp(凸组合) ≤ exp 的凸组合 + eps。           *)
(*   η 形主件直连 CW219 Varberg 锥核；w 形伴生件经 A.2 换形。        *)
(* ============================================================ *)

(* C.1 η 形逐 eps（前提位照抄源件：0 < η ≤ 1） *)
Lemma jens_two_point_eps : forall (eta x y eps : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                      (real_mult eta y)))
          (real_plus (real_plus (real_mult (real_plus real_one (real_opp eta))
                                            (cauchy_real_exp x))
                                (real_mult eta (cauchy_real_exp y)))
                     eps).
Proof.
  intros eta x y eps Heta_pos Heta_le Heps.
  exact (real_exp_two_point_cvx_eps x y eta Heta_pos Heta_le eps Heps).
Qed.

(* C.2 η 形 Bishop 收口（le_b） *)
Lemma jens_two_point : forall (eta x y : Real),
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp eta)) x)
                                        (real_mult eta y)))
            (real_plus (real_mult (real_plus real_one (real_opp eta))
                                  (cauchy_real_exp x))
                       (real_mult eta (cauchy_real_exp y))).
Proof.
  intros eta x y Heta_pos Heta_le.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (jens_two_point_eps eta x y eps Heta_pos Heta_le Heps).
Qed.

(* C.3 w 形逐 eps（0 ≤ w、0 < 1−w） *)
Lemma jens_two_point_w_eps : forall (w x y eps : Real),
  real_le real_zero w ->
  real_lt real_zero (real_plus real_one (real_opp w)) ->
  real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_plus (real_mult w x)
                                      (real_mult (real_plus real_one (real_opp w)) y)))
          (real_plus (real_plus (real_mult w (cauchy_real_exp x))
                                (real_mult (real_plus real_one (real_opp w))
                                           (cauchy_real_exp y)))
                     eps).
Proof.
  intros w x y eps Hw0 Hw1 Heps.
  (* 0 ≤ w ⟹ −w ≤ 0 ⟹ 1−w ≤ 1（种子 η ≤ 1 前提位） *)
  assert (Hnegw : real_le (real_opp w) real_zero).
  { apply (kl_le_eq_r (real_opp w) (real_opp real_zero) real_zero).
    - exact (real_opp_le_compat real_zero w Hw0).
    - exact real_opp_zero. }
  assert (Hwle1 : real_le (real_plus real_one (real_opp w)) real_one).
  { apply (kl_le_eq_r (real_plus real_one (real_opp w))
             (real_plus real_one real_zero) real_one).
    - exact (real_le_plus_compat real_one real_one (real_opp w) real_zero
                 (real_le_refl real_one) Hnegw).
    - apply real_plus_zero. }
  (* η := 1−w 代入种子，双侧沿 (1−(1−w)) == w 换形 *)
  pose proof (jens_two_point_eps (real_plus real_one (real_opp w)) x y eps
                Hw1 Hwle1 Heps) as Hcvx.
  apply (RealSetoid.real_le_compat
           (cauchy_real_exp (real_plus (real_mult (real_plus real_one (real_opp (real_plus real_one (real_opp w)))) x)
                                       (real_mult (real_plus real_one (real_opp w)) y)))
           (cauchy_real_exp (real_plus (real_mult w x)
                                       (real_mult (real_plus real_one (real_opp w)) y)))
           (real_plus (real_plus (real_mult (real_plus real_one (real_opp (real_plus real_one (real_opp w)))) (cauchy_real_exp x))
                                 (real_mult (real_plus real_one (real_opp w)) (cauchy_real_exp y)))
                      eps)
           (real_plus (real_plus (real_mult w (cauchy_real_exp x))
                                 (real_mult (real_plus real_one (real_opp w)) (cauchy_real_exp y)))
                      eps)).
  - apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_mult_compat
               (real_plus real_one (real_opp (real_plus real_one (real_opp w))))
               x w x).
      * exact (jens_ring_one_involut w).
      * apply real_eq_refl.
    + apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus real_one (real_opp (real_plus real_one (real_opp w))))
                 (cauchy_real_exp x) w (cauchy_real_exp x)).
        -- exact (jens_ring_one_involut w).
        -- apply real_eq_refl.
      * apply (RealSetoid.real_eq_mult_compat
                 (real_plus real_one (real_opp w)) (cauchy_real_exp y)
                 (real_plus real_one (real_opp w)) (cauchy_real_exp y)).
        -- apply real_eq_refl.
        -- apply real_eq_refl.
    + apply real_eq_refl.
  - exact Hcvx.
Qed.

(* C.4 w 形 Bishop 收口（le_b） *)
Lemma jens_two_point_w : forall (w x y : Real),
  real_le real_zero w ->
  real_lt real_zero (real_plus real_one (real_opp w)) ->
  real_le_b (cauchy_real_exp (real_plus (real_mult w x)
                                        (real_mult (real_plus real_one (real_opp w)) y)))
            (real_plus (real_mult w (cauchy_real_exp x))
                       (real_mult (real_plus real_one (real_opp w))
                                  (cauchy_real_exp y))).
Proof.
  intros w x y Hw0 Hw1.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (jens_two_point_w_eps w x y eps Hw0 Hw1 Heps).
Qed.

(* ============================================================ *)
(* Part D：主件 —— jens_weighted_n_point（加权 n 点 Jensen）         *)
(*   exp(Σ w_i·x_i) ≤_B Σ w_i·exp(x_i)                              *)
(*   （w_i ≥ 0、Σ w_i == 1；切线锥逐点化路线，零除法）。             *)
(* ============================================================ *)

Theorem jens_weighted_n_point_b : forall (X : Type) (w x : X -> Real) (l : list X),
  (forall a : X, real_le real_zero (w a)) ->
  real_eq (real_list_sum X w l) real_one ->
  real_le_b (cauchy_real_exp (real_list_sum X (fun a : X => real_mult (w a) (x a)) l))
            (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l).
Proof.
  intros X w x l Hw0 Hnorm.
  unfold real_le_b.
  set (z := real_list_sum X (fun a : X => real_mult (w a) (x a)) l).
  set (E := cauchy_real_exp z).
  set (S := real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l).
  (* 收口器 D := E，正性证书 exp z > 0（CW219 既有件） *)
  apply (real_le_closure_b E S E (cauchy_real_exp_pos z)).
  intros h Hh.
  set (t := fun a : X => real_plus (x a) (real_opp z)).
  (* 核换形：E·exp(t a) == exp(x a) *)
  assert (HexpE : forall a : X,
            real_eq (real_mult E (cauchy_real_exp (t a))) (cauchy_real_exp (x a))).
  { intro a.
    apply (real_eq_trans _ (cauchy_real_exp (real_plus z (t a))) _).
    - apply real_eq_sym.
      exact (cauchy_real_exp_plus z (t a)).
    - apply (cauchy_real_exp_wd (real_plus z (t a)) (x a)).
      exact (jens_ring_z_cancel z (x a)). }
  (* 逐点换形：w a·exp(x a) == E·(w a·exp(t a)) *)
  assert (FT : forall a : X,
            real_eq (real_mult (w a) (cauchy_real_exp (x a)))
                    (real_mult E (real_mult (w a) (cauchy_real_exp (t a))))).
  { intro a.
    apply (real_eq_trans _
             (real_mult (w a) (real_mult E (cauchy_real_exp (t a)))) _).
    - apply (RealSetoid.real_eq_mult_compat (w a) (cauchy_real_exp (x a))
               (w a) (real_mult E (cauchy_real_exp (t a)))).
      + apply real_eq_refl.
      + apply real_eq_sym.
        exact (HexpE a).
    - apply (real_eq_trans _
               (real_mult (real_mult (w a) E) (cauchy_real_exp (t a))) _).
      + apply real_mult_assoc.
      + apply (real_eq_trans _
                 (real_mult (real_mult E (w a)) (cauchy_real_exp (t a))) _).
        * apply (RealSetoid.real_eq_mult_compat (real_mult (w a) E)
                   (cauchy_real_exp (t a)) (real_mult E (w a))
                   (cauchy_real_exp (t a))).
          -- apply real_mult_comm.
          -- apply real_eq_refl.
        * apply real_eq_sym.
          exact (real_mult_assoc E (w a) (cauchy_real_exp (t a))).
  }
  (* 归一化坍缩核：Σ w_i·(x_i − z) == 0 *)
  assert (HN0 : real_eq (real_list_sum X (fun a : X => real_mult (w a) (t a)) l)
                        real_zero).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult (w a) (x a)) l)
                        (real_list_sum X (fun a : X => real_mult (w a) (real_opp z)) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_plus (real_mult (w a) (x a))
                                                        (real_mult (w a) (real_opp z))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a. apply real_distrib.
      + apply real_list_sum_add.
    - apply (real_eq_trans _ (real_plus z (real_opp z)) _).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply real_eq_refl.
        * apply (real_eq_trans _
                   (real_mult (real_opp z) (real_list_sum X w l)) _).
          -- exact (real_list_sum_linear_r X (real_opp z) w l).
          -- apply (real_eq_trans _ (real_mult (real_opp z) real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat (real_opp z)
                          (real_list_sum X w l) (real_opp z) real_one
                          (real_eq_refl (real_opp z)) Hnorm).
             ++ apply real_mult_one.
      + apply real_plus_opp. }
  (* 归一化坍缩：Σ w_i·(1 + x_i − z) == 1 *)
  assert (HN1 : real_eq (real_list_sum X (fun a : X => real_mult (w a)
                                            (real_plus real_one (t a))) l)
                        real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult (w a) real_one) l)
                        (real_list_sum X (fun a : X => real_mult (w a) (t a)) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_plus (real_mult (w a) real_one)
                                                        (real_mult (w a) (t a))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a. apply real_distrib.
      + apply real_list_sum_add.
    - apply (real_eq_trans _ (real_plus real_one real_zero) _).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * apply (real_eq_trans _
                   (real_mult real_one (real_list_sum X w l)) _).
          -- exact (real_list_sum_linear_r X real_one w l).
          -- apply (real_eq_trans _ (real_mult real_one real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat real_one
                          (real_list_sum X w l) real_one real_one
                          (real_eq_refl real_one) Hnorm).
             ++ apply real_mult_one.
        * exact HN0.
      + apply real_plus_zero. }
  (* 逐点切线 × 非负系数：f a ≤ g a *)
  assert (Hcpos : forall a : X, real_le real_zero (real_mult E (w a))).
  { intro a. exact (kl_le_mult_weak_swap (w a) E (Hw0 a) (cauchy_real_exp_pos z)). }
  assert (Hpt : forall a : X,
            real_le (real_mult (real_plus real_one (t a)) (real_mult E (w a)))
                    (real_mult (real_plus (cauchy_real_exp (t a)) h)
                               (real_mult E (w a)))).
  { intro a.
    apply real_le_mult_compat_weak.
    - exact (kl_le_mult_weak_swap (w a) E (Hw0 a) (cauchy_real_exp_pos z)).
    - exact (RealInterfaceEnhancedMod.real_exp_ge_linear_eps (t a) h Hh). }
  assert (Hsum : real_le (real_list_sum X (fun a : X => real_mult (real_plus real_one (t a)) (real_mult E (w a))) l)
                         (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l))
    by exact (real_list_sum_le X _ _ l Hpt).
  (* 左端 == E *)
  assert (HL : real_eq (real_list_sum X (fun a : X => real_mult (real_plus real_one (t a)) (real_mult E (w a))) l) E).
  { apply (real_eq_trans _
             (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (real_plus real_one (t a))) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (real_plus real_one (t a)))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a.
        apply (real_eq_trans _
                 (real_mult (real_mult E (w a)) (real_plus real_one (t a))) _).
        * apply real_mult_comm.
        * apply real_eq_sym.
          exact (real_mult_assoc E (w a) (real_plus real_one (t a))).
      + exact (real_list_sum_linear X E
                 (fun a : X => real_mult (w a) (real_plus real_one (t a))) l).
    - apply (real_eq_trans _ (real_mult E real_one) _).
      + apply (RealSetoid.real_eq_mult_compat E
                 (real_list_sum X (fun a : X => real_mult (w a) (real_plus real_one (t a))) l)
                 E real_one (real_eq_refl E) HN1).
      + apply real_mult_one. }
  (* 中段和恒等：Σ w·(exp t + h) == T + h（T := Σ w·exp t） *)
  assert (HTsum : real_eq
            (real_list_sum X (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l)
            (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l) h)).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l)
                        (real_list_sum X (fun a : X => real_mult (w a) h) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_plus (real_mult (w a) (cauchy_real_exp (t a)))
                                                        (real_mult (w a) h)) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a. apply real_distrib.
      + apply real_list_sum_add.
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      + apply real_eq_refl.
      + apply (real_eq_trans _ (real_mult h (real_list_sum X w l)) _).
        * exact (real_list_sum_linear_r X h w l).
        * apply (real_eq_trans _ (real_mult h real_one) _).
          -- apply (RealSetoid.real_eq_mult_compat h (real_list_sum X w l)
                       h real_one (real_eq_refl h) Hnorm).
          -- apply real_mult_one. }
  (* 右端 == S + E·h *)
  assert (HR : real_eq (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l)
                       (real_plus S (real_mult E h))).
  { apply (real_eq_trans _
             (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l)) _).
    - apply (real_eq_trans _
               (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (real_plus (cauchy_real_exp (t a)) h))) l) _).
      + apply (real_list_sum_ext X _ _ l).
        intro a.
        apply (real_eq_trans _
                 (real_mult (real_mult E (w a)) (real_plus (cauchy_real_exp (t a)) h)) _).
        * apply real_mult_comm.
        * apply real_eq_sym.
          exact (real_mult_assoc E (w a) (real_plus (cauchy_real_exp (t a)) h)).
      + exact (real_list_sum_linear X E
                 (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l).
    - apply (real_eq_trans _
               (real_mult E (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l) h)) _).
      + apply (RealSetoid.real_eq_mult_compat E
                 (real_list_sum X (fun a : X => real_mult (w a) (real_plus (cauchy_real_exp (t a)) h)) l)
                 E (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l) h)
                 (real_eq_refl E) HTsum).
      + apply (real_eq_trans _
                 (real_plus (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l))
                            (real_mult E h)) _).
        * apply real_distrib.
        * apply (RealSetoid.real_eq_plus_compat _ _ _ _).
          -- (* E·T == S：经 Σ(E·(w·exp t)) 桥（逐点 FT 反向 + linear 反向） *)
             apply (real_eq_trans
                      (real_mult E (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l))
                      (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (cauchy_real_exp (t a)))) l)
                      S).
            ++ apply real_eq_sym.
               exact (real_list_sum_linear X E
                        (fun a : X => real_mult (w a) (cauchy_real_exp (t a))) l).
            ++ apply (real_eq_trans
                        (real_list_sum X (fun a : X => real_mult E (real_mult (w a) (cauchy_real_exp (t a)))) l)
                        (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l)
                        S).
               ** apply (real_list_sum_ext X
                            (fun a : X => real_mult E (real_mult (w a) (cauchy_real_exp (t a))))
                            (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l).
                  intro a. apply real_eq_sym.
                  exact (FT a).
               ** apply real_eq_refl.
          -- apply real_eq_refl. }
  (* 合拢：E == Σf ≤ Σg == S + E·h，逐 h 收口 *)
  apply (kl_le_eq_r E
           (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l)
           (real_plus S (real_mult E h))).
  - apply (kl_le_eq_l
             (real_list_sum X (fun a : X => real_mult (real_plus real_one (t a)) (real_mult E (w a))) l)
             (real_list_sum X (fun a : X => real_mult (real_plus (cauchy_real_exp (t a)) h) (real_mult E (w a))) l) E).
    + exact Hsum.
    + exact HL.
  - exact HR.
Qed.

(* D.2 逐 eps 形（le_b 主件在给定 eps 的特化；Or 单向桥 inl 支） *)
Theorem jens_weighted_n_point : forall (X : Type) (w x : X -> Real) (l : list X),
  (forall a : X, real_le real_zero (w a)) ->
  real_eq (real_list_sum X w l) real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (cauchy_real_exp (real_list_sum X (fun a : X => real_mult (w a) (x a)) l))
          (real_plus (real_list_sum X (fun a : X => real_mult (w a) (cauchy_real_exp (x a))) l) eps).
Proof.
  intros X w x l Hw0 Hnorm eps Heps.
  apply (RealSetoid.real_lt_le_iff_req).
  left.
  exact (jens_weighted_n_point_b X w x l Hw0 Hnorm eps Heps).
Qed.

(* ============================================================ *)
(* Part E：旗舰 —— jens_partition（Σ π^{1−η}·π*^η ≤_B 1）            *)
(*   任意指标型 list X 泛化（CW219 nat-seq 版 → list X）+ le_b 收口。 *)
(*   路线：逐点 AM-GM（误差配权 eps·π_t，正权归一化吸收）             *)
(*   ⟹ Z ≤ (1−η)·Σπ + η·Σπ* + eps == 1 + eps。零除法零折半。        *)
(* ============================================================ *)

Theorem jens_partition_eps : forall (X : Type) (pit pist : X -> Real) (l : list X) (eta : Real)
    (Hpit : forall a : X, real_lt real_zero (pit a))
    (Hpist : forall a : X, real_lt real_zero (pist a)),
  real_eq (real_list_sum X pit l) real_one ->
  real_eq (real_list_sum X pist l) real_one ->
  real_lt real_zero eta -> real_le eta real_one ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_list_sum X
             (fun a : X => real_mult
                (real_pow_pos (pit a) (real_plus real_one (real_opp eta)) (Hpit a))
                (real_pow_pos (pist a) eta (Hpist a)))
             l)
          (real_plus real_one eps).
Proof.
  intros X pit pist l eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le eps Heps.
  set (m := real_plus real_one (real_opp eta)).
  (* 逐点 AM-GM，误差项配权 eps·pit a（正性：eps>0 × pit a>0） *)
  assert (Hpt : forall a : X,
            real_le (real_mult (real_pow_pos (pit a) m (Hpit a))
                               (real_pow_pos (pist a) eta (Hpist a)))
                    (real_plus (real_plus (real_mult m (pit a))
                                          (real_mult eta (pist a)))
                               (real_mult eps (pit a)))).
  { intro a.
    exact (real_amgm_pointwise_eps (pit a) (pist a) eta (Hpit a) (Hpist a)
             Heta_pos Heta_le (real_mult eps (pit a))
             (real_mult_positive eps (pit a) Heps (Hpit a))). }
  assert (Hsum : real_le
            (real_list_sum X (fun a : X => real_mult
                                (real_pow_pos (pit a) m (Hpit a))
                                (real_pow_pos (pist a) eta (Hpist a))) l)
            (real_list_sum X (fun a : X => real_plus
                                (real_plus (real_mult m (pit a))
                                           (real_mult eta (pist a)))
                                (real_mult eps (pit a))) l))
    by exact (real_list_sum_le X _ _ l Hpt).
  (* 拆分：Σ(f + g) == Σf + Σg *)
  assert (Hsplit : real_eq
            (real_list_sum X (fun a : X => real_plus
                                (real_plus (real_mult m (pit a))
                                           (real_mult eta (pist a)))
                                (real_mult eps (pit a))) l)
            (real_plus (real_list_sum X (fun a : X => real_plus
                                            (real_mult m (pit a))
                                            (real_mult eta (pist a))) l)
                       (real_list_sum X (fun a : X => real_mult eps (pit a)) l)))
    by exact (real_list_sum_add X _ _ l).
  (* Σf == m·Σpit + η·Σpist == m·1 + η·1 == m + η == 1 *)
  assert (Hf : real_eq (real_list_sum X (fun a : X => real_plus
                                            (real_mult m (pit a))
                                            (real_mult eta (pist a))) l)
                       real_one).
  { apply (real_eq_trans _
             (real_plus (real_list_sum X (fun a : X => real_mult m (pit a)) l)
                        (real_list_sum X (fun a : X => real_mult eta (pist a)) l)) _).
    - exact (real_list_sum_add X _ _ l).
    - apply (real_eq_trans _
                (real_plus (real_mult m (real_list_sum X pit l))
                           (real_mult eta (real_list_sum X pist l))) _).
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _).
        * exact (real_list_sum_linear X m pit l).
        * exact (real_list_sum_linear X eta pist l).
      + apply (real_eq_trans _ (real_plus m eta) _).
        * apply (RealSetoid.real_eq_plus_compat _ _ _ _).
          -- apply (real_eq_trans _ (real_mult m real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat m
                          (real_list_sum X pit l) m real_one
                          (real_eq_refl m) Hnormp).
             ++ apply real_mult_one.
          -- apply (real_eq_trans _ (real_mult eta real_one) _).
             ++ apply (RealSetoid.real_eq_mult_compat eta
                          (real_list_sum X pist l) eta real_one
                          (real_eq_refl eta) Hnormq).
             ++ apply real_mult_one.
        * exact (kl_ring_m_plus_eta eta). }
  (* Σg == eps·Σpit == eps·1 == eps *)
  assert (Hg : real_eq (real_list_sum X (fun a : X => real_mult eps (pit a)) l) eps).
  { apply (real_eq_trans _ (real_mult eps (real_list_sum X pit l)) _).
    - exact (real_list_sum_linear X eps pit l).
    - exact (real_eq_trans (real_mult eps (real_list_sum X pit l))
               (real_mult eps real_one) eps
               (RealSetoid.real_eq_mult_compat eps (real_list_sum X pit l)
                  eps real_one (real_eq_refl eps) Hnormp)
               (real_mult_one eps)). }
  (* 合拢：Z ≤ Σf + Σg == 1 + eps *)
  exact (kl_le_eq_r
           (real_list_sum X (fun a : X => real_mult
                                (real_pow_pos (pit a) m (Hpit a))
                                (real_pow_pos (pist a) eta (Hpist a))) l)
           (real_list_sum X (fun a : X => real_plus
                                (real_plus (real_mult m (pit a))
                                           (real_mult eta (pist a)))
                                (real_mult eps (pit a))) l)
           (real_plus real_one eps)
           Hsum
           (real_eq_trans _
              (real_plus (real_list_sum X (fun a : X => real_plus
                                              (real_mult m (pit a))
                                              (real_mult eta (pist a))) l)
                         (real_list_sum X (fun a : X => real_mult eps (pit a)) l))
              (real_plus real_one eps)
              Hsplit
              (RealSetoid.real_eq_plus_compat _ _ _ _ Hf Hg))).
Qed.

(* E.2 旗舰 Bishop 收口（le_b）：Σ π^{1−η}·π*^η ≤_B 1
   ——定理 4.8 step_kl_eta_bound 的数学核（le_b/eps 形；Or 形精确
   收口构造性不可证，判词见 UpRealLeB 尾注台账）。 *)
Theorem jens_partition : forall (X : Type) (pit pist : X -> Real) (l : list X) (eta : Real)
    (Hpit : forall a : X, real_lt real_zero (pit a))
    (Hpist : forall a : X, real_lt real_zero (pist a)),
  real_eq (real_list_sum X pit l) real_one ->
  real_eq (real_list_sum X pist l) real_one ->
  real_lt real_zero eta -> real_le eta real_one ->
  real_le_b (real_list_sum X
               (fun a : X => real_mult
                  (real_pow_pos (pit a) (real_plus real_one (real_opp eta)) (Hpit a))
                  (real_pow_pos (pist a) eta (Hpist a)))
               l)
            real_one.
Proof.
  intros X pit pist l eta Hpit Hpist Hnormp Hnormq Heta_pos Heta_le.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (jens_partition_eps X pit pist l eta Hpit Hpist Hnormp Hnormq
           Heta_pos Heta_le eps Heps).
Qed.

(* ============================================================ *)
(* 尾注：诚实台账（本席增量判词 + 沉淀卡索引回填行）                   *)
(*                                                                *)
(* 【判词 J1｜方向勘误④】任务书原式 Σ w exp(−x) ≤ exp(−Σw x) + eps    *)
(*   为 Jensen 反向、一般假（数值反例在案）；本席按真值方向            *)
(*   exp(Σw x) ≤ Σ w exp(x) + eps 陈述并全件贯通——沿 CW220 M0.1      *)
(*   「假命题修正」先例，勘误后目标（Bishop 形凸性 + 旗舰 Z ≤ 1）     *)
(*   不变且恰为可证方向。                                            *)
(* 【判词 J2｜切线锥逐点化】主件路线 = 切线下界（保底件2）×非负系数    *)
(*   （kl_le_mult_weak_swap）×求和（real_list_sum_le）×归一化坍缩     *)
(*   （HN0/HN1）×D 形收口器（D := exp z，证书 cauchy 实测正性）：      *)
(*   相比「n=1 基例 + cons 归约两点」的归纳路线，免除法/重归一化/      *)
(*   误差 1/n 拆分三座山，全链零除法；cons 归纳路线中重归一化          *)
(*   w_i/(1−w_a) 的除法面在本路线不出现。                            *)
(* 【判词 J3｜逐 eps 统一余量】主件收口器面取 h := eps 全称位实例，    *)
(*   与 sumb_ 判词 S1 同源：real_le_b 全称面余量可复制，无需          *)
(*   构造性对半。                                                    *)
(* 【判词 J4｜旗舰泛化边界】CW219 real_interp_Z_le_one_eps 系          *)
(*   nat 索引 seq 0 n 特化；本席 jens_partition 泛化至任意指标型      *)
(*   list X（real_list_sum 引擎本就 X 首参泛型，逐点/求和/坍缩       *)
(*   三段全泛化直迁），并与 UpRealLeB real_interp_Z_le_one_B          *)
(*   （E.18）互为特化关系——E.18 消费本件只需 X := nat、              *)
(*   l := seq 0 n 单步实例（本席未回改既有文件）。                    *)
(* 【判词 J5｜两点件增量边界】两点凸性 eps 形核 CW219 已有             *)
(*   （real_exp_two_point_cvx_eps，Varberg 锥）；本席增量为           *)
(*   le_b 收口双形（C.2/C.4）+ w 参数形伴生（C.3/C.4，含             *)
(*   1−(1−w) == w 换形核 A.2 与 0 ≤ w ⟹ 1−w ≤ 1 链）。               *)
(* 【机器状态】四关卡：G1 禁词全零（含头注注记位）；G2 重编 EXIT=0；   *)
(*   G3 提取探针 Obj.magic 计数零；G4 coqchk 认证通过（见交付报告）。  *)
(* 沉淀卡索引回填行（备卡尾）：                                       *)
(*   E389（拟）：jens_ 十件全绿——le_b Jensen 有限离散族               *)
(*   （tangent/two_point 双形/w 形/n 点双形/partition 双形），         *)
(*   切线锥逐点化定式（免除法 n 点路线）首次沉淀；                     *)
(*   消费面：step_kl_eta_bound_B 数学核、UpStepKL 插值族泛化位。       *)
(* ============================================================ *)

Print Assumptions jens_exp_tangent_eps.
Print Assumptions jens_exp_tangent.
Print Assumptions jens_two_point_eps.
Print Assumptions jens_two_point.
Print Assumptions jens_two_point_w_eps.
Print Assumptions jens_two_point_w.
Print Assumptions jens_weighted_n_point_b.
Print Assumptions jens_weighted_n_point.
Print Assumptions jens_partition_eps.
Print Assumptions jens_partition.

(* ======== G07_KLWall 成员件：UpReqKLStrict（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqKLStrict.v —— KL>0 严格引理席（评审08 P1.6）：Gibbs 族严格化   *)
(*   与 eps 形引擎 real_gibbs_inequality_B（UpRealLeB E.13）成对的      *)
(*   「能量非常数 ⟹ KL > 0」缺口的第一批严格件。                        *)
(*                                                                *)
(* 主结果（全 Set 层、零 Prop 表出面、零新公理）：                      *)
(*   A. klst_ep_two_terms：Q 层二阶部分和下界 n≥2、x≥0 ⟹              *)
(*        1+x+x²/2 ≤ exp_partial n x（严格切线的间隙源）。              *)
(*   B. klst_exp_tangent_pos：0<w ⟹ 1+w < e^w（严格指数切线正支；        *)
(*        间隙见证 δ := eps²/2）；klst_log_tangent_pos：1<x ⟹            *)
(*        log x < x−1（严格对数切线正支；x == e^{log x} 换形）。          *)
(*   C. klst_gibbs_core_strict：p<q ⟹ 0 < kl_term(p,q)+(q−p)            *)
(*        （严格 Gibbs 逐点核 q>p 支：g == p·((x−1)−log x)、x=q/p>1）；   *)
(*        klst_gibbs_core_zero：p==q ⟹ kl_term(p,q)+(q−p)==0            *)
(*        （退化对照件；log(1)==0 经 real_log_wd）。与 C 成对。           *)
(*   D. klst_kl_sum_strict：KL 严格正主件——逐项正性 + 双归一化 +          *)
(*        逐项 p≤q（弱序 Or 形，排除 q>p 支）+ s₀ 处严格分离见证          *)
(*        （p s₀ < q s₀）⟹ 0 < Σ_s kl_term（表 l₁++s₀::l₂）。            *)
(*                                                                *)
(* 【阻塞精确裁决】逐项 g≥0 的 q<p 支需要「负 argument 严格指数切线」     *)
(*   e^{−t} > 1−t（t>0），等价于对数下切线 log y > 1−1/y（y>1）即对数     *)
(*   上切线 x<1 侧；其 Q 层间隙源需四项交错部分和下界                     *)
(*   1−t+t²/2−t³/6 ≤ ep_n(−t)，现有 exp_partial 族仅一阶                 *)
(*   （exp_partial_ge_plus_x）与符号分段非严格件（odd/even_ge_minus），   *)
(*   无正间隙见证 ⟹ 主件逐项前提以弱序 p≤q 形承载（排除 q>p 支），        *)
(*   无条件「能量非常数⟹KL>0」留待该单引理补齐（邻接件，判词见尾注）。    *)
(*   接口对照：exp 严格单调字段已有（cauchy_real_exp_mono）；缺严格切线    *)
(*   字段（real_exp_ge_linear_eps 为 eps 形 Or 编码，等号分支不可提取——   *)
(*   UpRealLeB 尾注同一已知限制在严格层的显形）。                        *)
(*                                                                *)
(* 红线：零公理零未闭合证明；Set 层语句（real_lt 为 sigT 见证集值）；     *)
(*   全 Qed. 闭合；Print Assumptions 须 Closed。                        *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Import ListNotations.

(* ============================================================ *)
(* Part A：Q 层二阶部分和下界（严格切线的间隙源）                       *)
(* ============================================================ *)

Lemma klst_ep_two_terms : forall (m : nat) (x : Q),
  Qle 0 x ->
  Qle (1 + x + x * x * (1#2))
      (exp_partial (Datatypes.S (Datatypes.S m)) x).
Proof.
  intros m x Hx.
  induction m as [| m IH].
  - apply (qeq_le _ _).
    cbn [exp_partial q_pow q_fact].
    unfold Qdiv, Qminus.
    simpl.
    field.
  - assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m))) x ==
                    exp_partial (Datatypes.S (Datatypes.S m)) x +
                    q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                    q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))).
    { cbn [exp_partial]. reflexivity. }
    setoid_rewrite Hstep.
    (* Qle A (B + T)：经 Qle_trans 拆成 Qle A B（IH）与 Qle B (B + T)；      *)
    (* 后者再经 Qle_trans 过 (B + 0)（qeq_le 环换形杀 +0 失配）              *)
    (* + Qplus_le_r 0 T B 的 proj1（iff 正向）供 0 ≤ T 入场。               *)
    apply (Qle_trans (1 + x + x * x * (1#2))
                     (exp_partial (Datatypes.S (Datatypes.S m)) x)
                     (exp_partial (Datatypes.S (Datatypes.S m)) x +
                      q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                      q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))).
    + exact IH.
    + apply (Qle_trans (exp_partial (Datatypes.S (Datatypes.S m)) x)
                       (exp_partial (Datatypes.S (Datatypes.S m)) x + 0)%Q
                       (exp_partial (Datatypes.S (Datatypes.S m)) x +
                        q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                        q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))).
      * apply (qeq_le (exp_partial (Datatypes.S (Datatypes.S m)) x)
                      (exp_partial (Datatypes.S (Datatypes.S m)) x + 0)%Q).
        ring.
      * apply (proj2 (Qplus_le_r 0%Q
                        (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m))) /
                         q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))
                        (exp_partial (Datatypes.S (Datatypes.S m)) x))).
        apply (q_pow_fact_nonneg x (Datatypes.S (Datatypes.S (Datatypes.S m))) Hx).
Qed.

(* ============================================================ *)
(* Part B：严格指数/对数切线（正 argument 支）                          *)
(* ============================================================ *)

Lemma klst_exp_tangent_pos : forall w : Real,
  real_lt real_zero w ->
  real_lt (real_plus real_one w) (cauchy_real_exp w).
Proof.
  intros [u Hu] Hw.
  destruct Hw as [eps [Heps [N0 HN0]]].
  exists (eps * eps * (1#2)).
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (eps * eps) (1#2)).
    + apply (Qmult_lt_0_compat eps eps).
      * apply QltT_to_Qlt. exact Heps.
      * apply QltT_to_Qlt. exact Heps.
    + unfold Qlt. simpl. lia.
  - exists (Nat.max N0 2).
    intros n Hn.
    apply Qlt_to_QltT.
    assert (Hmax : (Nat.max N0 2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
    assert (HnN0 : (N0 <= n)%nat) by lia.
    assert (Hn2 : (2 <= n)%nat) by lia.
    destruct n as [| [| m]]; [ lia | lia | ].
    (* HN0 结论形为 QltT eps (u k − 0)：QltT 为 Id bool，不可 unfolds 直用，   *)
    (* 经 b5a_QltT_eq_r（x==y ⟹ QltT a y ⟹ QltT a x）+ Q 环换形去 −0。       *)
    assert (Hun0m : QltT eps (u (Datatypes.S (Datatypes.S m)) - 0))
      by (apply (HN0 (Datatypes.S (Datatypes.S m))); apply NatLe_lift; exact HnN0).
    assert (HunT : QltT eps (u (Datatypes.S (Datatypes.S m))))
      by (apply (b5a_QltT_eq_r eps (u (Datatypes.S (Datatypes.S m))) (u (Datatypes.S (Datatypes.S m)) - 0));
          [ ring | exact Hun0m ]).
    assert (HunQ : Qlt eps (u (Datatypes.S (Datatypes.S m)))) by (apply QltT_to_Qlt; exact HunT).
    assert (Hun0 : Qle 0 (u (Datatypes.S (Datatypes.S m)))).
    { apply (Qle_trans 0 eps (u (Datatypes.S (Datatypes.S m)))).
      - apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
      - apply (Qlt_le_weak eps (u (Datatypes.S (Datatypes.S m)))). exact HunQ. }
    assert (Htwo : Qle (1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                       (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m)))))
      by exact (klst_ep_two_terms m (u (Datatypes.S (Datatypes.S m))) Hun0).
    assert (Hsq : Qlt (eps * eps) (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)))).
    { apply (Qmult_lt_compat_nonneg eps (u (Datatypes.S (Datatypes.S m))) eps (u (Datatypes.S (Datatypes.S m)))).
      - split.
        + apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        + exact HunQ.
      - split.
        + apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        + exact HunQ. }
    assert (Hhalf : Qlt 0 (1#2)) by (unfold Qlt; simpl; lia).
    assert (Hscale : Qlt (eps * eps * (1#2))
                         (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2)))
      by exact (Qmult_lt_compat_r (eps * eps) (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m))) (1#2)
                                  Hhalf Hsq).
    assert (Hproj : (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) (Datatypes.S (Datatypes.S m))
                     - projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) (Datatypes.S (Datatypes.S m))) ==
                    (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
    { setoid_rewrite (real_plus_proj real_one (existT (fun s : Qseq => cauchy s) u Hu) (Datatypes.S (Datatypes.S m))).
      cbn [projT1 cauchy_real_exp real_one].
      unfold Qminus. ring. }
    rewrite Hproj.
    (* 收尾：Hscale（严格）+ Htwo 左乘平移（Qplus_le_compat 嵌套，形状逐位对齐） *)
    apply (Qlt_le_trans (eps * eps * (1#2))
                        (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                        (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
    + exact Hscale.
    + apply (Qle_trans (u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                       ((1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                          + (- 1) + (- u (Datatypes.S (Datatypes.S m))))
                       (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1) + (- u (Datatypes.S (Datatypes.S m))))).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat
                 ((1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2)) + (- 1))
                 (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))) + (- 1))
                 (- u (Datatypes.S (Datatypes.S m))) (- u (Datatypes.S (Datatypes.S m)))).
        -- apply (Qplus_le_compat (1 + u (Datatypes.S (Datatypes.S m)) + u (Datatypes.S (Datatypes.S m)) * u (Datatypes.S (Datatypes.S m)) * (1#2))
                                 (exp_partial (Datatypes.S (Datatypes.S m)) (u (Datatypes.S (Datatypes.S m))))
                                 (- 1) (- 1)).
           ++ exact Htwo.
           ++ apply Qle_refl.
        -- apply Qle_refl.
Qed.

Lemma klst_log_tangent_pos : forall (x : Real)
  (Hx : real_lt real_zero x) (H1x : real_lt real_one x),
  real_lt (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx H1x.
  assert (Hu : real_lt real_zero (real_log x Hx)).
  { apply (RealSetoid.real_lt_id_l real_zero (real_log real_one real_lt_zero_one) (real_log x Hx)).
    - apply real_eq_sym. exact (real_log_one real_lt_zero_one).
    - exact (real_log_lt_mono real_one x real_lt_zero_one Hx H1x). }
  assert (Hexp : real_lt (real_plus real_one (real_log x Hx)) (cauchy_real_exp (real_log x Hx)))
    by exact (klst_exp_tangent_pos (real_log x Hx) Hu).
  assert (Hval : real_eq (cauchy_real_exp (real_log x Hx)) x)
    by exact (cw_log_exp_right x Hx).
  assert (H2 : real_lt (real_plus real_one (real_log x Hx)) x)
    by exact (RealSetoid.real_lt_compat (real_plus real_one (real_log x Hx))
                                        (real_plus real_one (real_log x Hx))
                                        (cauchy_real_exp (real_log x Hx)) x
                                        (real_eq_refl (real_plus real_one (real_log x Hx)))
                                        Hval Hexp).
  apply (RealSetoid.real_lt_compat (real_log x Hx) (real_log x Hx)
                                   (real_plus (real_opp real_one) x)
                                   (real_plus x (real_opp real_one))).
  - apply real_eq_refl.
  - exact (real_plus_comm (real_opp real_one) x).
  - apply (RealSetoid.real_lt_id_l (real_log x Hx)
               (real_plus (real_opp real_one) (real_plus real_one (real_log x Hx)))
               (real_plus (real_opp real_one) x)).
    + apply real_eq_sym.
      apply (real_eq_trans _ (real_plus (real_plus (real_opp real_one) real_one) (real_log x Hx)) _).
      * apply real_plus_assoc.
      * apply (real_eq_trans _ (real_plus real_zero (real_log x Hx)) _).
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp real_one) real_one)
                                                (real_log x Hx)
                                                real_zero (real_log x Hx)).
           ++ apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
              ** apply real_plus_comm.
              ** apply real_plus_opp.
           ++ apply real_eq_refl.
        -- apply (real_eq_trans _ (real_plus (real_log x Hx) real_zero) _).
           ++ apply real_plus_comm.
           ++ apply real_plus_zero.
    + apply (real_lt_plus_translate (real_opp real_one)
                                    (real_plus real_one (real_log x Hx)) x).
      exact H2.
Qed.

(* ============================================================ *)
(* Part C0：实层换形微型助手（逐点 exact 恒等，Q 环收尾）                *)
(*   注：real_inv_pos 的投影带 if leb 分支，逐点 q == p·(q·inv p) 非恒等，  *)
(*   故 gap_shape 的换形不得走 real_eq_of_zero_diff，须在实层经            *)
(*   assoc/comm/one/inv_pos_correct 链完成（klst_r_pqx_eq_q）。           *)
(* ============================================================ *)

Lemma klst_r_mult_distr_l : forall (p a b : Real),
  real_eq (real_mult p (real_plus a b))
          (real_plus (real_mult p a) (real_mult p b)).
Proof.
  intros p a b. apply real_eq_of_zero_diff. intro n.
  repeat (rewrite (real_mult_proj _ _ n) || rewrite (real_plus_proj _ _ n)
          || rewrite (real_opp_proj _ n)).
  unfold Qminus. ring.
Qed.

Lemma klst_r_mult_opp_r : forall (p a : Real),
  real_eq (real_mult p (real_opp a)) (real_opp (real_mult p a)).
Proof.
  intros p a. apply real_eq_of_zero_diff. intro n.
  repeat (rewrite (real_mult_proj _ _ n) || rewrite (real_plus_proj _ _ n)
          || rewrite (real_opp_proj _ n)).
  unfold Qminus. ring.
Qed.

Lemma klst_r_mult_m1_r : forall (p : Real),
  real_eq (real_mult p (real_opp real_one)) (real_opp p).
Proof.
  intro p. apply real_eq_of_zero_diff. intro n.
  repeat (rewrite (real_mult_proj _ _ n) || rewrite (real_plus_proj _ _ n)
          || rewrite (real_opp_proj _ n)).
  cbn [projT1 real_one].
  unfold Qminus. ring.
Qed.

Lemma klst_r_pqx_eq_q : forall (p q : Real) (Hp : real_lt real_zero p),
  real_eq (real_mult p (real_mult q (real_inv_pos p Hp))) q.
Proof.
  intros p q Hp.
  apply (real_eq_trans _ (real_mult q (real_mult p (real_inv_pos p Hp))) _).
  - apply (real_eq_trans _ (real_mult (real_mult p q) (real_inv_pos p Hp)) _).
    + exact (real_mult_assoc p q (real_inv_pos p Hp)).
    + apply (real_eq_trans _ (real_mult (real_mult q p) (real_inv_pos p Hp)) _).
      * apply (RealSetoid.real_eq_mult_compat (real_mult p q) (real_inv_pos p Hp)
                                             (real_mult q p) (real_inv_pos p Hp)).
        -- exact (real_mult_comm p q).
        -- apply real_eq_refl.
      * apply real_eq_sym. exact (real_mult_assoc q p (real_inv_pos p Hp)).
  - apply (real_eq_trans _ (real_mult q real_one) _).
    + apply (RealSetoid.real_eq_mult_compat q (real_mult p (real_inv_pos p Hp))
                                            q real_one).
      * apply real_eq_refl.
      * exact (real_inv_pos_correct p Hp).
    + exact (real_mult_one q).
Qed.

Lemma klst_r_opp_minus : forall (a b : Real),
  real_eq (real_plus b (real_opp a)) (real_opp (real_plus a (real_opp b))).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  repeat (rewrite (real_mult_proj _ _ n) || rewrite (real_plus_proj _ _ n)
          || rewrite (real_opp_proj _ n)).
  unfold Qminus. ring.
Qed.

(* 严格 + 弱序相加：0 < x、0 ≤ y ⟹ 0 < x + y
   （real_lt_plus_compat_lt_le 的结论带 (0+0)，经 real_lt_id_l + real_plus_zero 换形） *)
Lemma klst_r_lt_plus_le : forall (x y : Real),
  real_lt real_zero x -> real_le real_zero y -> real_lt real_zero (real_plus x y).
Proof.
  intros x y Hx Hy.
  apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero) (real_plus x y)).
  - apply real_eq_sym. exact (real_plus_zero real_zero).
  - exact (real_lt_plus_compat_lt_le real_zero x real_zero y Hx Hy).
Qed.

(* ============================================================ *)
(* Part C：严格 Gibbs 逐点核（q>p 支）+ 退化对照                        *)
(* ============================================================ *)

(* 环形换形（实层 eq 链：分配率 + 乘 −1 + 乘 −log + p·(q·inv p) == q）：  *)
(*   kl_term(p,q) + (q − p) == p·((x−1) − log x)，x := q·inv(p)。        *)
Lemma klst_gap_shape : forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
          (real_mult p (real_plus (real_plus (real_mult q (real_inv_pos p Hp)) (real_opp real_one))
                                  (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                                      (real_mult_positive q (real_inv_pos p Hp) Hq
                                                        (real_inv_pos_pos p Hp)))))).
Proof.
  intros p q Hp Hq.
  unfold real_kl_term.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  apply (real_eq_trans
           _ (real_plus (real_opp (real_mult p L))
                        (real_plus (real_mult p X) (real_opp p))) _).
  - (* 左形：p·(−L) + (q + −p) → −(p·L) + (p·X + −p) *)
    apply (RealSetoid.real_eq_plus_compat (real_mult p (real_opp L))
                                          (real_plus q (real_opp p))
                                          (real_opp (real_mult p L))
                                          (real_plus (real_mult p X) (real_opp p))).
    + exact (klst_r_mult_opp_r p L).
    + apply (RealSetoid.real_eq_plus_compat q (real_opp p) (real_mult p X) (real_opp p)).
      * apply real_eq_sym. exact (klst_r_pqx_eq_q p q Hp).
      * apply real_eq_refl.
  - (* 右形：p·((X + −1) + −L) → (p·(X+−1)) + p·(−L) → (p·X + −p) + −(p·L)，再交换合流 *)
    apply real_eq_sym.
    apply (real_eq_trans
             _ (real_plus (real_mult p (real_plus X (real_opp real_one)))
                          (real_mult p (real_opp L))) _).
    + exact (klst_r_mult_distr_l p (real_plus X (real_opp real_one)) (real_opp L)).
    + apply (real_eq_trans
               _ (real_plus (real_plus (real_mult p X) (real_opp p))
                            (real_opp (real_mult p L))) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult p (real_plus X (real_opp real_one)))
                 (real_mult p (real_opp L))
                 (real_plus (real_mult p X) (real_opp p))
                 (real_opp (real_mult p L))).
        -- apply (real_eq_trans
                    _ (real_plus (real_mult p X) (real_mult p (real_opp real_one))) _).
           ++ exact (klst_r_mult_distr_l p X (real_opp real_one)).
           ++ apply (RealSetoid.real_eq_plus_compat (real_mult p X)
                       (real_mult p (real_opp real_one)) (real_mult p X) (real_opp p)).
              ** apply real_eq_refl.
              ** exact (klst_r_mult_m1_r p).
        -- exact (klst_r_mult_opp_r p L).
      * apply real_plus_comm.
Qed.

Lemma klst_gibbs_core_strict : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_lt p q),
  real_lt real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hpq.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  assert (Hxpos : real_lt real_zero X) by exact HX.
  assert (Hx1 : real_lt real_one X).
  { apply (RealSetoid.real_lt_id_l real_one (real_mult p (real_inv_pos p Hp)) X).
    - apply real_eq_sym. exact (real_inv_pos_correct p Hp).
    - exact (real_mult_lt_compat p q (real_inv_pos p Hp) Hpq (real_inv_pos_pos p Hp)). }
  assert (Htan : real_lt L (real_plus X (real_opp real_one)))
    by exact (klst_log_tangent_pos X HX Hx1).
  assert (Hgap : real_lt real_zero (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (real_opp L) (real_plus X (real_opp real_one)))
             (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
    - apply real_plus_comm.
    - apply (RealSetoid.real_lt_id_l real_zero
               (real_plus (real_opp L) L)
               (real_plus (real_opp L) (real_plus X (real_opp real_one)))).
      + apply real_eq_sym.
        apply (real_eq_trans _ (real_plus L (real_opp L)) _).
        * apply real_plus_comm.
        * apply real_plus_opp.
      + exact (real_lt_plus_translate (real_opp L) L (real_plus X (real_opp real_one)) Htan). }
  assert (Hprod : real_lt real_zero (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L))))
    by exact (real_mult_pos_compat p
                (real_plus (real_plus X (real_opp real_one)) (real_opp L))
                Hp Hgap).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L)))
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
  - exact Hprod.
Qed.

(* 退化对照件：p == q ⟹ kl_term(p,q) + (q − p) == 0（与严格件成对）。 *)
Lemma klst_gibbs_core_zero : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hpq : real_eq p q),
  real_eq (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))) real_zero.
Proof.
  intros p q Hp Hq Hpq.
  unfold real_kl_term.
  set (x := real_mult q (real_inv_pos p Hp)).
  set (Hx := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  (* x == 1：p==q 换 inv（inv_pos_ext）+ inv_pos_correct *)
  assert (Hx1 : real_eq x real_one).
  { unfold x.
    apply (real_eq_trans _ (real_mult q (real_inv_pos q Hq)) _).
    - apply (RealSetoid.real_eq_mult_compat q (real_inv_pos p Hp) q (real_inv_pos q Hq)).
      + apply real_eq_refl.
      + exact (real_inv_pos_ext p q Hp Hq Hpq).
    - exact (real_inv_pos_correct q Hq). }
  (* 逐点环：L_n == 0 注入（log x == log 1 == 0） *)
  assert (Hlog0 : real_eq (real_log x Hx) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact (real_log_wd x real_one Hx real_lt_zero_one Hx1).
    - exact (real_log_one real_lt_zero_one). }
  (* 实层换形链：g == p·(−log x) + q − p == p·(−log 1) + q − p
     == p·0 + q − p == q − p == q − q == 0 *)
  apply (real_eq_trans
           _ (real_plus (real_mult p (real_opp (real_log real_one real_lt_zero_one)))
                        (real_plus q (real_opp p))) _).
  { apply (RealSetoid.real_eq_plus_compat
             (real_mult p (real_opp (real_log x Hx)))
             (real_plus q (real_opp p))
             (real_mult p (real_opp (real_log real_one real_lt_zero_one)))
             (real_plus q (real_opp p))).
    - apply (RealSetoid.real_eq_mult_compat p (real_opp (real_log x Hx))
                                            p (real_opp (real_log real_one real_lt_zero_one))).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_opp_compat _ _).
        exact (real_log_wd x real_one Hx real_lt_zero_one Hx1).
    - apply real_eq_refl. }
  apply (real_eq_trans
           _ (real_plus (real_mult p (real_opp real_zero)) (real_plus q (real_opp p))) _).
  { apply (RealSetoid.real_eq_plus_compat
             (real_mult p (real_opp (real_log real_one real_lt_zero_one)))
             (real_plus q (real_opp p))
             (real_mult p (real_opp real_zero))
             (real_plus q (real_opp p))).
    - apply (RealSetoid.real_eq_mult_compat p (real_opp (real_log real_one real_lt_zero_one))
                                            p (real_opp real_zero)).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_opp_compat _ _). exact (real_log_one real_lt_zero_one).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_plus real_zero (real_plus q (real_opp p))) _).
  { apply (RealSetoid.real_eq_plus_compat (real_mult p (real_opp real_zero))
                                         (real_plus q (real_opp p))
                                         real_zero (real_plus q (real_opp p))).
    - apply (real_eq_trans _ (real_mult p real_zero) _).
      + apply (RealSetoid.real_eq_mult_compat p (real_opp real_zero) p real_zero).
        * apply real_eq_refl.
        * exact real_opp_zero.
      + exact (real_mult_zero p).
    - apply real_eq_refl. }
  apply (real_eq_trans _ (real_plus q (real_opp p)) _).
  { apply (real_eq_trans _ (real_plus (real_plus q (real_opp p)) real_zero) _).
    - apply real_plus_comm.
    - apply real_plus_zero. }
  apply (real_eq_trans _ (real_plus q (real_opp q)) _).
  { apply (RealSetoid.real_eq_plus_compat q (real_opp p) q (real_opp q)).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_opp_compat p q). exact Hpq. }
  apply real_plus_opp.
Qed.

(* ============================================================ *)
(* Part D：KL 严格和主件（弱序 p≤q 支）                                 *)
(* ============================================================ *)

Lemma klst_list_sum_app : forall (X : Type) (f : X -> Real) (l₁ l₂ : list X),
  real_eq (real_list_sum X f (l₁ ++ l₂))
          (real_plus (real_list_sum X f l₁) (real_list_sum X f l₂)).
Proof.
  intros X f l₁ l₂.
  induction l₁ as [| w rest IH]; cbn [app real_list_sum].
  - apply (real_eq_sym _ _).
    apply (real_eq_trans _ (real_plus (real_list_sum X f l₂) real_zero) _).
    + apply real_plus_comm.
    + apply real_plus_zero.
  - apply (real_eq_trans
             _ (real_plus (f w) (real_plus (real_list_sum X f rest) (real_list_sum X f l₂))) _).
    + apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum X f (rest ++ l₂))
                                            (f w) (real_plus (real_list_sum X f rest) (real_list_sum X f l₂))).
      * apply real_eq_refl.
      * exact IH.
    + apply real_plus_assoc.
Qed.

(* KL 严格正主件：逐项正性 + 双归一化 + 逐项 p≤q（弱序，排除 q>p 支）+
   s₀ 处严格分离见证（p s₀ < q s₀）⟹ 0 < Σ_s kl_term。 *)
Lemma klst_kl_sum_strict : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, real_le (p s) (q s))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : real_lt (p s₀) (q s₀)),
  real_lt real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  set (L := l₁ ++ s₀ :: l₂).
  set (KL := fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : X => real_plus (KL s) (real_plus (q s) (real_opp (p s)))).
  (* 1. 逐项 g ≥ 0（弱序两支：严格支 C / 等号支退化件） *)
  assert (Hgnonneg : forall s : X, real_le real_zero (G s)).
  { intro s. unfold G. destruct (Hpq s) as [Hlt | Heq].
    - unfold real_le. left.
      exact (klst_gibbs_core_strict (p s) (q s) (Hp s) (Hq s) Hlt).
    - unfold real_le. right. apply real_eq_sym.
      exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s) Heq). }
  (* 2. Σ kl L == Σ G L（归一化零和抵消，gibbs_inequality_eps 同款） *)
  assert (Hzero : real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L) real_zero).
  { apply (real_eq_trans _ (real_plus (real_list_sum X p L) (real_list_sum X (fun s => real_opp (q s)) L)) _).
    - apply (real_list_sum_add X p (fun s => real_opp (q s)) L).
    - apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p L)
                                             (real_list_sum X (fun s => real_opp (q s)) L)
                                             real_one (real_opp real_one)).
        * exact Hnormp.
        * apply (real_eq_trans _ (real_opp (real_list_sum X q L)) _).
          -- apply (real_list_sum_opp X q L).
          -- apply (RealSetoid.real_eq_opp_compat (real_list_sum X q L) real_one).
             exact Hnormq.
      + apply real_plus_opp. }
  assert (Hqp : real_eq (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L) real_zero).
  { apply (real_eq_trans _ (real_list_sum X (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L) _).
    - apply (real_list_sum_ext X (fun s => real_plus (q s) (real_opp (p s)))
                               (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L).
      intro s. exact (klst_r_opp_minus (p s) (q s)).
    - apply (real_eq_trans _ (real_opp (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)) _).
      + apply (real_list_sum_opp X (fun s => real_plus (p s) (real_opp (q s))) L).
      + apply (real_eq_trans _ (real_opp real_zero) _).
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)
                                               real_zero).
          exact Hzero.
        * exact real_opp_zero. }
  assert (HsumG : real_eq (real_list_sum X KL L) (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_list_sum X KL L)
                          (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)) _).
    - apply (real_eq_trans _ (real_plus (real_list_sum X KL L) real_zero) _).
      + apply real_eq_sym. apply real_plus_zero.
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X KL L) real_zero
                                              (real_list_sum X KL L)
                                              (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)).
        * apply real_eq_refl.
        * apply real_eq_sym. exact Hqp.
    - apply (real_eq_sym _ _). unfold G.
      apply (real_list_sum_add X KL (fun s => real_plus (q s) (real_opp (p s))) L). }
  (* 3. Σ G L == G s₀ + Σ G l₁ + Σ G l₂（app 拆分 + assoc + comm） *)
  assert (Hsplit : real_eq (real_list_sum X G L)
                           (real_plus (real_plus (G s₀) (real_list_sum X G l₁))
                                      (real_list_sum X G l₂))).
  { unfold L.
    apply (real_eq_trans _ (real_plus (real_list_sum X G l₁)
                                      (real_plus (G s₀) (real_list_sum X G l₂))) _).
    - exact (klst_list_sum_app X G l₁ (s₀ :: l₂)).
    - apply (real_eq_trans
               _ (real_plus (real_plus (real_list_sum X G l₁) (G s₀)) (real_list_sum X G l₂)) _).
      + apply real_plus_assoc.
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_list_sum X G l₁) (G s₀))
                                             (real_list_sum X G l₂)
                                             (real_plus (G s₀) (real_list_sum X G l₁))
                                             (real_list_sum X G l₂)).
        * apply real_plus_comm.
        * apply real_eq_refl. }
  (* 4. 尾和 ≥ 0 + 严格项 ⟹ 0 < Σ G L ⟹ 0 < Σ kl L *)
  assert (Htail : real_le real_zero (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
  { apply (RealSetoid.real_le_id_r real_zero (real_list_sum X G (l₁ ++ l₂))
                                   (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - exact (klst_list_sum_app X G l₁ l₂).
    - exact (real_list_sum_nonneg X G (l₁ ++ l₂) Hgnonneg). }
  assert (Hmain : real_lt real_zero (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))).
  { apply (klst_r_lt_plus_le (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - unfold G. unfold KL.
      exact (klst_gibbs_core_strict (p s₀) (q s₀) (Hp s₀) (Hq s₀) Hdiv).
    - exact Htail. }
  assert (Hfin : real_eq (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
                         (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_plus (G s₀) (real_list_sum X G l₁)) (real_list_sum X G l₂)) _).
    - apply real_plus_assoc.
    - apply real_eq_sym. exact Hsplit. }
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
           (real_list_sum X KL L)).
  - apply (real_eq_trans _ (real_list_sum X G L) _).
    + exact Hfin.
    + apply real_eq_sym. exact HsumG.
  - exact Hmain.
Qed.

(* ============================================================ *)
(* 闭合证明（Print Assumptions 须全 Closed）                            *)
(* ============================================================ *)

Print Assumptions klst_ep_two_terms.
Print Assumptions klst_exp_tangent_pos.
Print Assumptions klst_log_tangent_pos.
Print Assumptions klst_r_mult_distr_l.
Print Assumptions klst_r_mult_opp_r.
Print Assumptions klst_r_mult_m1_r.
Print Assumptions klst_r_pqx_eq_q.
Print Assumptions klst_r_opp_minus.
Print Assumptions klst_r_lt_plus_le.
Print Assumptions klst_gap_shape.
Print Assumptions klst_gibbs_core_strict.
Print Assumptions klst_gibbs_core_zero.
Print Assumptions klst_list_sum_app.
Print Assumptions klst_kl_sum_strict.

(* ============================================================ *)
(* 尾注（判词台账）                                                    *)
(*   判词 1（正支全链绿）：严格指数/对数切线正支 + 严格 Gibbs 核 q>p 支 +   *)
(*     退化对照件 + KL 严格和（弱序 p≤q 支）全 Qed，零假设位——            *)
(*     「能量非常数 ⟹ KL>0」在 p≤q 侧已完整闭合。                        *)
(*     勘误（续席收口）：①Part A 步进 case 以 Qle_trans 过 (B+0)           *)
(*     （qeq_le 环换形 + Qplus_le_r 0 T B proj1）清偿 A+0 失配；           *)
(*     ②gap_shape 的 real_eq_of_zero_diff 路线证伪（real_inv_pos 投影带    *)
(*     if leb 分支，逐点 q == p·q·inv p 非恒等），改实层链               *)
(*     （C0 五件：distr_l / mult_opp_r / mult_m1_r / pqx_eq_q /           *)
(*     opp_minus，前四者经 assoc/comm/one/inv_pos_correct，               *)
(*     opp_minus 逐点 exact）；③klst_log_tangent_pos 换形链两处            *)
(*     (−1)+1 / 0+x 形位以 comm+opp / comm+zero 重排；④Part D 拆和/      *)
(*     平移各件以 real_list_sum_ext + real_opp_zero 桥 Σ(q−p)==0，        *)
(*     s₀ 严格项直接注入 gibbs_core_strict（Hdiv 即其 Hpq 实参）。         *)
(*   判词 2（负支阻塞精确裁决）：q<p 支的逐项 g≥0 需负 argument 严格指数    *)
(*     切线 e^{−t} > 1−t（t>0）；等价形：对数下切线 log y > 1−1/y（y>1）   *)
(*     ＝ 对数上切线 x<1 侧。其 Q 层间隙源需四项交错部分和下界             *)
(*     1−t+t²/2−t³/6 ≤ ep_n(−t)；现有 exp_partial 族仅一阶                *)
(*     （exp_partial_ge_plus_x，L34891）与符号分段非严格件                *)
(*     （odd/even_ge_minus，L40707/L40814，服务 eps 形 non-strict），     *)
(*     无正间隙见证字段 ⟹ 单引理缺口，补齐后与 Part D 逐项前提换全称弱序    *)
(*     即得无条件件（温度桥：β₂<β₁、E₀<E₁ ⟹ 比率严格分离，               *)
(*     cauchy_real_exp_mono 严格单调已备，exp_neg 反号换形一路可通）。     *)
(*   判词 3（与 eps 形引擎关系）：本件不消费 real_le_b 收口器——严格层      *)
(*     real_lt 为 sigT 正陈述，无 Or 等号分支提取障碍；障碍在库侧切线      *)
(*     字段缺失（real_exp_ge_linear_eps / real_log_le_linear_eps 均为     *)
(*     eps 形 Or 编码），与 UpRealLeB 尾注已知限制同源不同位。             *)
(* ============================================================ *)

(* ======== G07_KLWall 成员件：UpReqKLEnergy（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpReqKLEnergy.v —— KL>0 无条件收口席（UpReqKLStrict 判词 2 负支缺口）  *)
(*                                                                *)
(* 主结果（全 Set 层、零 Prop 表出面、零新公理，14 件全 Qed）：         *)
(*   A. klst_q_pair_nonneg（Q）：t^k/k! − t^{k+1}/(k+1)! ≥ 0           *)
(*      （0≤t≤1；q_pair2_nonneg 的一般指数版，四项下界的配对引擎）。    *)
(*   B. Q 层符号微型件五件：klst_q_pow_pos（t>0 ⟹ t^k>0）、            *)
(*      klst_q_pow_neg_even / klst_q_pow_neg_odd（(−t) 偶/奇幂符号）、  *)
(*      klst_q_lt0_opp / klst_q_div_lt0。                              *)
(*   C. klst_ep_four_terms（Q）：【缺口单引理】                          *)
(*        1 − t + t²/2 − t³/6 ≤ exp_partial (S(S(S m))) (−t)           *)
(*      （0 ≤ t ≤ 1；即 1−t+t²/2−t³/6 ≤ ep_n(−t) 对全体 n≥3 成立。      *)
(*      截断方向裁决：exp_partial n x 为前 n+1 项部分和（k=0..n），      *)
(*      负 argument 交错级数的下侧截断取奇号三项截断 S₃；n=3 处恒等式   *)
(*      入场，奇号子列两步单调升（配对项 = A），偶号项 = 奇号前项 +      *)
(*      正尾项。Witness：m 任意（n=3+m 构造性给出）。                    *)
(*   D. klst_exp_tangent_neg（Real）：w < 0 ⟹ 1 + w < e^w               *)
(*      （负 argument 严格指数切线。分离见证 δ 分支构造：               *)
(*      eps0²/3 ≤ 1/(2C) 时取 δ := eps0²/6，否则 δ := 1/(2C)；          *)
(*      t := −u_n ≤ 1 支走 C，t > 1 支：奇号走 exp_partial_odd_lower    *)
(*      （1/(2C) 正下界，M/C/m0 由 real_norm_bounded / exp_series_arch  *)
(*      / exp_partial_tail_small 供给），偶号由「奇号项 = 偶号项 +      *)
(*      负尾商」反号传递同获 1/(2C)。全体 n ≥ max(N0, 2m0+3) 一致。）   *)
(*   E. klst_log_tangent_neg（Real）：0 < x < 1 ⟹ log x < x − 1         *)
(*      （对数上切线 x<1 侧；w := log x < 0 经 D + e^{log x}==x 换形）。*)
(*   F. klst_gibbs_core_strict_neg（Real）：q < p ⟹ 0 < kl_term+(q−p)   *)
(*      （严格 Gibbs 逐点核 q<p 支；x := q·inv p < 1，经 E +            *)
(*      klst_gap_shape 同型收口——与 klst_gibbs_core_strict 成对）。     *)
(*   G. klst_kl_energy_nonconst（Real，无条件主件）：                    *)
(*        双归一化 + 逐项全称弱序（p≤q ∨ q≤p 双向可比）+                *)
(*        s₀ 处严格分离（任一方向；能量非常数的比率分离见证）            *)
(*        ⟹ 0 < Σ_s kl_term。                                          *)
(*      相对 UpReqKLStrict.klst_kl_sum_strict：逐项前提由单向弱序       *)
(*      （p≤q）换全称双向弱序；排除支 q>p 由 F 补齐——温度桥两向         *)
(*      （β₂<β₁、E₀<E1 时高温端 p s₀ < q s₀ 与低温端 q s₀ < p s₀）      *)
(*      均入主件。s₀ 分离前提以 Set 层 Or 承载（实序不可判定，           *)
(*      诚实接口位；具体 Gibbs 实例经 cauchy_real_exp_mono 严格单调     *)
(*      消解）。                                                        *)
(*                                                                *)
(* 红线：零公理零未闭合证明；Real 层语句全 Set（real_lt 为 sigT）；      *)
(*   Q 层沿用库内 Q 层先例（QltT 判定 + Qle 阶信念不出现在 Real 层）；   *)
(*   全 Qed 闭合；Print Assumptions 须全 Closed。                        *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.

Import ListNotations.

(* ============================================================ *)
(* Part A：Q 层配对非负（一般指数版）                                   *)
(* ============================================================ *)

Lemma klst_q_pair_nonneg : forall (t : Q) (k : nat),
  Qle 0 t -> Qle t 1 ->
  Qle 0 (q_pow t k / q_fact k - q_pow t (Datatypes.S k) / q_fact (Datatypes.S k)).
Proof.
  intros t k Ht0 Ht1.
  apply (proj1 (Qle_minus_iff (q_pow t (Datatypes.S k) / q_fact (Datatypes.S k))
                              (q_pow t k / q_fact k))).
  apply (q_le_div_le (q_pow t (Datatypes.S k)) (q_fact (Datatypes.S k))
                     (q_pow t k) (q_fact k)).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - assert (Hpow : q_pow t (Datatypes.S k) == t * q_pow t k).
    { apply (q_pow_succ t k). }
    setoid_rewrite Hpow.
    setoid_replace (q_fact (Datatypes.S k))
      with ((Z.of_nat (Datatypes.S k) # 1) * q_fact k).
    2: { apply (q_fact_succ k). }
    setoid_replace (t * q_pow t k * q_fact k)
      with (t * (q_pow t k * q_fact k)). 2: ring.
    setoid_replace (q_pow t k * ((Z.of_nat (Datatypes.S k) # 1) * q_fact k))
      with ((Z.of_nat (Datatypes.S k) # 1) * (q_pow t k * q_fact k)). 2: ring.
    apply (Qmult_le_compat_r t (Z.of_nat (Datatypes.S k) # 1)
                             (q_pow t k * q_fact k)).
    * apply (Qle_trans _ 1 _).
      + exact Ht1.
      + unfold Qle. simpl. lia.
    * apply Qmult_le_0_compat.
      + apply q_pow_nonneg. exact Ht0.
      + apply (Qlt_le_weak 0 (q_fact k)). apply q_fact_pos.
Qed.

(* ============================================================ *)
(* Part B：Q 层符号微型件                                               *)
(* ============================================================ *)

Lemma klst_q_pow_pos : forall (t : Q) (k : nat),
  Qlt 0 t -> Qlt 0 (q_pow t k).
Proof.
  intros t k Ht.
  induction k as [| k IH].
  - unfold Qlt. simpl. lia.
  - cbn [q_pow].
    apply (Qmult_lt_0_compat t (q_pow t k)).
    + exact Ht.
    + exact IH.
Qed.

Lemma klst_q_pow_neg_even : forall (t : Q) (j : nat),
  q_pow (- t) (2 * j) == q_pow t (2 * j).
Proof.
  intros t j.
  induction j as [| j IH].
  - reflexivity.
  - replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    cbn [q_pow].
    setoid_rewrite IH.
    ring.
Qed.

Lemma klst_q_pow_neg_odd : forall (t : Q) (j : nat),
  q_pow (- t) (Datatypes.S (2 * j)) == - (q_pow t (Datatypes.S (2 * j))).
Proof.
  intros t j.
  cbn [q_pow].
  setoid_rewrite (klst_q_pow_neg_even t j).
  ring.
Qed.

Lemma klst_q_pow_neg_odd_lt : forall (t : Q) (j : nat),
  Qlt 0 t -> Qlt (q_pow (- t) (Datatypes.S (2 * j))) 0.
Proof.
  intros t j Ht.
  setoid_rewrite (klst_q_pow_neg_odd t j).
  apply (proj2 (Qlt_minus_iff (- (q_pow t (Datatypes.S (2 * j)))) 0)).
  assert (Hsh : 0 - (- (q_pow t (Datatypes.S (2 * j)))) == q_pow t (Datatypes.S (2 * j)))
    by (unfold Qminus; ring).
  setoid_rewrite Hsh.
  apply klst_q_pow_pos. exact Ht.
Qed.

Lemma klst_q_lt0_opp : forall a : Q, Qlt a 0 -> Qlt 0 (- a).
Proof.
  intros a H.
  apply (proj2 (Qlt_minus_iff 0 (- a))).
  assert (Hsh : (- a) - 0 == 0 - a) by (unfold Qminus; ring).
  setoid_rewrite Hsh.
  apply (proj1 (Qlt_minus_iff a 0)).
  exact H.
Qed.

Lemma klst_q_div_lt0 : forall (a b : Q),
  Qlt a 0 -> Qlt 0 b -> Qlt (a / b) 0.
Proof.
  intros a b Ha Hb.
  unfold Qdiv.
  apply (proj2 (Qlt_minus_iff (a * Qinv b) 0)).
  assert (Hsh : 0 - a * Qinv b == (- a) * Qinv b) by (unfold Qminus; ring).
  setoid_rewrite Hsh.
  apply (Qmult_lt_0_compat (- a) (Qinv b)).
  - exact (klst_q_lt0_opp a Ha).
  - apply Qinv_lt_0_compat. exact Hb.
Qed.

(* ============================================================ *)
(* Part C：【缺口单引理】四项交错部分和下界（Q 层）                      *)
(*   1 − t + t²/2 − t³/6 ≤ exp_partial n (−t)（0≤t≤1、n≥3 全体）        *)
(* ============================================================ *)

(* 奇号子列（n = 2j+3）：两步单调升。步进恒等式 cbn 双侧归一同型；        *)
(* 新增配对 = t^{2j+4}/(2j+4)! − t^{2j+5}/(2j+5)! ≥ 0（klst_q_pair_nonneg）。 *)
Lemma klst_ep_four_terms_odd : forall (j : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  Qle (1 - t + t * t * (1#2) - t * t * t * (1#6))
      (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t)).
Proof.
  intros j t Ht0 Ht1.
  induction j as [| j IH].
  - apply (qeq_le _ _).
    cbn [exp_partial q_pow q_fact].
    unfold Qdiv, Qminus.
    simpl.
    field.
  - assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) (- t) ==
                    exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                    (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                    (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
    { cbn [exp_partial]. reflexivity. }
    replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    setoid_rewrite Hstep.
    apply (Qle_trans (1 - t + t * t * (1#2) - t * t * t * (1#6))
                     (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                     ((exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                       (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))) +
                      (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))))).
    + exact IH.
    + apply (Qle_trans
               (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
               (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                ((q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                 (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))))
               ((exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                 (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))) +
                (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))))).
      * apply (Qle_trans
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) + 0)
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                  ((q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                   (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))))).
        -- apply (qeq_le _ _). ring.
        -- apply (proj2 (Qplus_le_r 0%Q
                            ((q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) +
                             (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))))
                            (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t)))).
           replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat
             with (2 * Datatypes.S (Datatypes.S j))%nat by lia.
           setoid_rewrite (klst_q_pow_neg_even t (Datatypes.S (Datatypes.S j))).
           setoid_rewrite (klst_q_pow_neg_odd t (Datatypes.S (Datatypes.S j))).
           setoid_replace
             ((- q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j))))
             with
             (- (q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))))
             by (unfold Qdiv; ring).
           assert (Hpair : Qle 0
                     (q_pow t (2 * Datatypes.S (Datatypes.S j)) / q_fact (2 * Datatypes.S (Datatypes.S j)) -
                      q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))))
             by exact (klst_q_pair_nonneg t (2 * Datatypes.S (Datatypes.S j)) Ht0 Ht1).
           apply (Qle_trans 0%Q
                     (q_pow t (2 * Datatypes.S (Datatypes.S j)) / q_fact (2 * Datatypes.S (Datatypes.S j)) -
                      q_pow t (Datatypes.S (2 * Datatypes.S (Datatypes.S j))) / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j))))).
           { exact Hpair. }
           { apply qeq_le. unfold Qminus. reflexivity. }
      * apply (qeq_le _ _). ring.
Qed.

(* 偶号项（n = 2j+4）：= 奇号前项 + 正尾项（(−t)^{2j+4} = t^{2j+4} ≥ 0）。 *)
Lemma klst_ep_four_terms_even : forall (j : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  Qle (1 - t + t * t * (1#2) - t * t * t * (1#6))
      (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) (- t)).
Proof.
  intros j t Ht0 Ht1.
  assert (Hstep : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) (- t) ==
                  exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                  (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
  { cbn [exp_partial]. reflexivity. }
  apply (Qle_trans (1 - t + t * t * (1#2) - t * t * t * (1#6))
                   (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                   (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) (- t))).
  - exact (klst_ep_four_terms_odd j t Ht0 Ht1).
  - setoid_rewrite Hstep.
    apply (Qle_trans (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t))
                     (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) + 0)
                     (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t) +
                      (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
    + apply (qeq_le _ _). ring.
    + apply (proj2 (Qplus_le_r 0%Q
                      (q_pow (- t) (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                      (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) (- t)))).
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat
        with (2 * Datatypes.S (Datatypes.S j))%nat by lia.
      setoid_rewrite (klst_q_pow_neg_even t (Datatypes.S (Datatypes.S j))).
      apply q_div_nonneg.
      * apply q_pow_nonneg. exact Ht0.
      * apply q_fact_pos.
Qed.

(* 缺口单引理（主形式）：对全体 n ≥ 3（n = 3 + m 由 m 奇偶分派）。 *)
Lemma klst_ep_four_terms : forall (m : nat) (t : Q),
  Qle 0 t -> Qle t 1 ->
  Qle (1 - t + t * t * (1#2) - t * t * t * (1#6))
      (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m))) (- t)).
Proof.
  intros m t Ht0 Ht1.
  destruct (Nat.even m) eqn:En.
  - apply Nat.even_spec in En. destruct En as [j Hj]. subst m.
    exact (klst_ep_four_terms_odd j t Ht0 Ht1).
  - assert (Hodd : Nat.odd m = true).
    { destruct (Nat.odd m) eqn:Eo.
      - reflexivity.
      - exfalso.
        rewrite <- Nat.negb_odd in En.
        rewrite Eo in En.
        simpl in En.
        discriminate En. }
    apply Nat.odd_spec in Hodd. destruct Hodd as [j Hj]. subst m.
    replace (2 * j + 1)%nat with (Datatypes.S (2 * j))%nat by lia.
    exact (klst_ep_four_terms_even j t Ht0 Ht1).
Qed.

(* ============================================================ *)
(* Part D：负 argument 严格指数切线（Real 层）                           *)
(*   w < 0 ⟹ 1 + w < e^w                                                *)
(* ============================================================ *)

Lemma klst_exp_tangent_neg : forall w : Real,
  real_lt w real_zero ->
  real_lt (real_plus real_one w) (cauchy_real_exp w).
Proof.
  intros [u Hu] Hw.
  destruct Hw as [eps0 [Heps0 [N0 HN0]]].
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu)) as [M [HMpos HM]].
  destruct (exp_series_arch M (qltT_leT' 0 M HMpos)) as [C [HC1 HC]].
  destruct (exp_partial_tail_small M C (qltT_leT' 0 M HMpos) HC1) as [m0 Hm0].
  assert (Heps0Q : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  assert (HC2pos : Qlt 0 (2 * C)).
  { apply (Qmult_lt_0_compat 2 C).
    - unfold Qlt; simpl; lia.
    - apply (Qlt_le_trans _ 1 _); [reflexivity | exact (QleT'_to_Qle _ _ HC1)]. }
  assert (HinvC : Qlt 0 (1 / (2 * C))).
  { unfold Qdiv.
    apply (Qmult_lt_0_compat 1 (Qinv (2 * C))).
    - unfold Qlt; simpl; lia.
    - apply Qinv_lt_0_compat. exact HC2pos. }
  assert (Hthird : Qlt 0 (eps0 * eps0 * (1#3))).
  { apply (Qmult_lt_0_compat (eps0 * eps0) (1#3)).
    - apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0.
    - unfold Qlt; simpl; lia. }
  assert (Hsixth : Qlt 0 (eps0 * eps0 * (1#6))).
  { apply (Qmult_lt_0_compat (eps0 * eps0) (1#6)).
    - apply (Qmult_lt_0_compat eps0 eps0); apply QltT_to_Qlt; exact Heps0.
    - unfold Qlt; simpl; lia. }
  assert (Hdstrict : Qlt (eps0 * eps0 * (1#6)) (eps0 * eps0 * (1#3))).
  { apply (proj2 (Qlt_minus_iff (eps0 * eps0 * (1#6)) (eps0 * eps0 * (1#3)))).
    assert (Hsh : (eps0 * eps0 * (1#3)) - (eps0 * eps0 * (1#6)) == eps0 * eps0 * (1#6))
      by ring.
    setoid_rewrite Hsh.
    exact Hsixth. }
  assert (Hmain : forall d : Q,
    Qle d (1 / (2 * C)) ->
    Qlt d (eps0 * eps0 * (1#3)) ->
    forall n : nat, (Nat.max N0 (2 * m0 + 3) <= n)%nat ->
    QltT d (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) n -
            projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) n)).
  { intros d Hd1 Hdlt n Hn.
    apply Qlt_to_QltT.
    assert (Hmax : (Nat.max N0 (2 * m0 + 3) <= n)%nat) by exact Hn.
    assert (HnN0 : (N0 <= n)%nat) by lia.
    assert (Hnbig : (2 * m0 + 3 <= n)%nat) by lia.
    assert (Hn3 : (3 <= n)%nat) by lia.
    assert (Hzero : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    assert (Hun0 : QltT eps0 (0 - u n)).
    { apply (b5a_QltT_eq_r eps0 (0 - u n) (projT1 real_zero n - u n)).
      - setoid_rewrite Hzero. reflexivity.
      - exact (HN0 n (NatLe_lift _ _ HnN0)). }
    assert (HtltT : QltT eps0 (- u n))
      by (apply (b5a_QltT_eq_r eps0 (- u n) (0 - u n));
          [ unfold Qminus; ring | exact Hun0 ]).
    assert (Ht0 : Qlt 0 (- u n)).
    { apply (Qlt_trans 0 eps0 (- u n)).
      - exact Heps0Q.
      - exact (QltT_to_Qlt eps0 (- u n) HtltT). }
    assert (Ht0le : Qle 0 (- u n)) by (apply (Qlt_le_weak 0 (- u n)); exact Ht0).
    assert (Hproj : (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) n -
                     projT1 (real_plus real_one (existT (fun s : Qseq => cauchy s) u Hu)) n) ==
                    (exp_partial n (u n) - (1 + u n))).
    { setoid_rewrite (real_plus_proj real_one (existT (fun s : Qseq => cauchy s) u Hu) n).
      cbn [projT1 cauchy_real_exp real_one].
      unfold Qminus. ring. }
    setoid_rewrite Hproj.
    assert (Hfin : exp_partial n (u n) - (1 + u n) ==
                   (exp_partial n (u n) + (- u n - 1)))
      by (unfold Qminus; ring).
    setoid_rewrite Hfin.
    destruct n as [| [| [| m]]]; [ exfalso; lia | exfalso; lia | exfalso; lia | ].
    destruct (Qlt_le_dec 1 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
      as [Ht1big | Ht1small].
    - (* t := −u_n > 1：奇号 1/(2C) 正下界 + 偶号反号传递 *)
      destruct (Nat.even (Datatypes.S (Datatypes.S (Datatypes.S m)))) eqn:En.
      + apply Nat.even_spec in En. destruct En as [m2 Hm2].
        rewrite Hm2.
        rewrite Hm2 in Hnbig, Ht0, Ht0le, Ht1big.
        assert (Hm2big : (m0 + 2 <= m2)%nat) by lia.
        assert (Hide : (Datatypes.S (2 * m2) = 2 * m2 + 1)%nat) by lia.
        assert (Hgt1 : Qlt (1 / (2 * C)) (exp_partial (2 * m2 + 1)%nat (u (2 * m2)%nat))).
        { apply (exp_partial_odd_lower M C m0 m2 (u (2 * m2)%nat)
                   (qltT_leT' 0 M HMpos) HC1 HC Hm0).
          - lia.
          - exact (HM (2 * m2)%nat). }
        assert (Hstep : exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat) ==
                        exp_partial (2 * m2)%nat (u (2 * m2)%nat) +
                        q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2)))
          by (cbn [exp_partial]; reflexivity).
        assert (Hquot : Qlt (q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2))) 0).
        { apply klst_q_div_lt0.
          - assert (Hux : u (2 * m2)%nat == - (- u (2 * m2)%nat)) by ring.
            setoid_rewrite Hux at 1.
            exact (klst_q_pow_neg_odd_lt (- u (2 * m2)%nat) m2 Ht0).
          - apply q_fact_pos. }
        assert (Hdown : Qlt (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat))
                            (exp_partial (2 * m2)%nat (u (2 * m2)%nat))).
        { apply (proj2 (Qlt_minus_iff (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat))
                                      (exp_partial (2 * m2)%nat (u (2 * m2)%nat)))).
          setoid_rewrite Hstep.
          assert (Hsh : exp_partial (2 * m2)%nat (u (2 * m2)%nat) -
                        (exp_partial (2 * m2)%nat (u (2 * m2)%nat) +
                         q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2))) ==
                        - (q_pow (u (2 * m2)%nat) (Datatypes.S (2 * m2)) / q_fact (Datatypes.S (2 * m2))))
            by (unfold Qminus; ring).
          setoid_rewrite Hsh.
          apply klst_q_lt0_opp. exact Hquot. }
        assert (Hgt1' : Qlt (1 / (2 * C)) (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat))).
        { rewrite Hide. exact Hgt1. }
        assert (Hgt : Qlt (1 / (2 * C)) (exp_partial (2 * m2)%nat (u (2 * m2)%nat)))
          by (apply (Qlt_trans _ (exp_partial (Datatypes.S (2 * m2)) (u (2 * m2)%nat)));
              [ exact Hgt1' | exact Hdown ]).
        assert (Hmid : Qlt (1 / (2 * C) + (- u (2 * m2)%nat - 1))
                           (exp_partial (2 * m2)%nat (u (2 * m2)%nat) + (- u (2 * m2)%nat - 1))).
        { apply (proj2 (Qlt_minus_iff (1 / (2 * C) + (- u (2 * m2)%nat - 1))
                                      (exp_partial (2 * m2)%nat (u (2 * m2)%nat) + (- u (2 * m2)%nat - 1)))).
          assert (Hsh : exp_partial (2 * m2)%nat (u (2 * m2)%nat) + (- u (2 * m2)%nat - 1) -
                        (1 / (2 * C) + (- u (2 * m2)%nat - 1)) ==
                        exp_partial (2 * m2)%nat (u (2 * m2)%nat) - 1 / (2 * C))
            by (unfold Qminus; ring).
          setoid_rewrite Hsh.
          apply (proj1 (Qlt_minus_iff (1 / (2 * C)) (exp_partial (2 * m2)%nat (u (2 * m2)%nat)))).
          exact Hgt. }
        apply (Qlt_trans _ (1 / (2 * C) + (- u (2 * m2)%nat - 1))).
        * apply (Qle_lt_trans _ (1 / (2 * C))).
          -- exact Hd1.
          -- apply (proj2 (Qlt_minus_iff (1 / (2 * C)) (1 / (2 * C) + (- u (2 * m2)%nat - 1)))).
             assert (Hsh : (1 / (2 * C) + (- u (2 * m2)%nat - 1)) - 1 / (2 * C) == (- u (2 * m2)%nat - 1))
               by (unfold Qminus; ring).
             setoid_rewrite Hsh.
             apply (proj1 (Qlt_minus_iff 1 (- u (2 * m2)%nat))). exact Ht1big.
        * exact Hmid.
      + assert (Hodd : Nat.odd (Datatypes.S (Datatypes.S (Datatypes.S m))) = true).
        { destruct (Nat.odd (Datatypes.S (Datatypes.S (Datatypes.S m)))) eqn:Eo.
          - reflexivity.
          - exfalso.
            rewrite <- Nat.negb_odd in En.
            rewrite Eo in En.
            simpl in En.
            discriminate En. }
        apply Nat.odd_spec in Hodd. destruct Hodd as [m2 Hm2].
        rewrite Hm2.
        rewrite Hm2 in Hnbig, Ht0, Ht0le, Ht1big.
        assert (Hm2big : (m0 + 1 <= m2)%nat) by lia.
        assert (Hgt : Qlt (1 / (2 * C)) (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat))).
        { apply (exp_partial_odd_lower M C m0 m2 (u (2 * m2 + 1)%nat)
                   (qltT_leT' 0 M HMpos) HC1 HC Hm0).
          - lia.
          - exact (HM (2 * m2 + 1)%nat). }
        assert (Hmid : Qlt (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1))
                           (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) + (- u (2 * m2 + 1)%nat - 1))).
        { apply (proj2 (Qlt_minus_iff (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1))
                                      (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) + (- u (2 * m2 + 1)%nat - 1)))).
          assert (Hsh : exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) + (- u (2 * m2 + 1)%nat - 1) -
                        (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1)) ==
                        exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat) - 1 / (2 * C))
            by (unfold Qminus; ring).
          setoid_rewrite Hsh.
          apply (proj1 (Qlt_minus_iff (1 / (2 * C)) (exp_partial (2 * m2 + 1)%nat (u (2 * m2 + 1)%nat)))).
          exact Hgt. }
        apply (Qlt_trans _ (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1))).
        * apply (Qle_lt_trans _ (1 / (2 * C))).
          -- exact Hd1.
          -- apply (proj2 (Qlt_minus_iff (1 / (2 * C)) (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1)))).
             assert (Hsh : (1 / (2 * C) + (- u (2 * m2 + 1)%nat - 1)) - 1 / (2 * C) == (- u (2 * m2 + 1)%nat - 1))
               by (unfold Qminus; ring).
             setoid_rewrite Hsh.
             apply (proj1 (Qlt_minus_iff 1 (- u (2 * m2 + 1)%nat))). exact Ht1big.
        * exact Hmid.
    - (* t := −u_n ≤ 1：四项下界（缺口单引理）直入 *)
      assert (Hfour : Qle (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                             + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                             - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                          (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                       (u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
      { apply (Qle_trans _
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                              (- (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))) _).
        - exact (klst_ep_four_terms m
                    (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) Ht0le Ht1small).
        - apply qeq_le.
          apply (exp_partial_wd (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                (- (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                                (u (Datatypes.S (Datatypes.S (Datatypes.S m))))).
          ring. }
      (* HmidA：CUBIC − (1 − t) ≤ G_n（Qplus_le_compat + 平移项同一形；t := −u_n 显式） *)
      assert (HmidA : Qle (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                             + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                             - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                             + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))
                          (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                       (u (Datatypes.S (Datatypes.S (Datatypes.S m)))) + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))).
      { apply (Qplus_le_compat
                 (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                    + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                    - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                 (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                              (u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                 (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                 (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
        - exact Hfour.
        - apply Qle_refl. }
      assert (HshapeA : (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))
                           + (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                           - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                           + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))
                        == ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                            - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)))
        by ring.
      assert (HshapeB : (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                       (u (Datatypes.S (Datatypes.S (Datatypes.S m)))) + (- (1 + u (Datatypes.S (Datatypes.S (Datatypes.S m))))))
                        == (exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m)))
                                        (u (Datatypes.S (Datatypes.S (Datatypes.S m)))) + (- u (Datatypes.S (Datatypes.S (Datatypes.S m))) - 1)))
        by ring.
      setoid_rewrite HshapeA in HmidA.
      setoid_rewrite HshapeB in HmidA.
      (* (−u)²·½ − (−u)³·⅙ ≥ eps0²·⅓ > d *)
      assert (Hmid1 : Qle (eps0 * eps0 * (1#3))
                          ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                           - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))).
      { assert (HA : Qle (eps0 * eps0)
                         ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * eps0)).
        { apply (Qmult_le_compat_r eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) eps0).
          - exact (Qlt_le_weak eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (QltT_to_Qlt eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) HtltT)).
          - exact (Qlt_le_weak 0 eps0 Heps0Q). }
        assert (HB : Qle (eps0 * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))
                         ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
        { apply (Qmult_le_compat_r eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))).
          - exact (Qlt_le_weak eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (QltT_to_Qlt eps0 (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) HtltT)).
          - exact Ht0le. }
        apply (Qle_trans _ ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#3)) _).
        { apply (Qmult_le_compat_r (eps0 * eps0)
                                   ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))) (1#3)).
          - apply (Qle_trans _ ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * eps0)).
            + exact HA.
            + apply (Qle_trans _ (eps0 * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
              * apply (qeq_le _ _). ring.
              * exact HB.
          - unfold Qle; simpl; lia. }
        apply (proj2 (Qle_minus_iff ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#3))
                       ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                        - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)))).
        assert (Hpos : Qle 0 ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                              * (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))))).
        { apply (Qmult_le_0_compat
                   ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                   (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
          + apply (Qmult_le_0_compat
                     ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))) (1#6)).
            * apply (Qmult_le_0_compat (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) (- u (Datatypes.S (Datatypes.S (Datatypes.S m))))).
              -- exact Ht0le.
              -- exact Ht0le.
            * apply (Qlt_le_weak 0 (1#6)). unfold Qlt; simpl; lia.
          + apply (proj1 (Qle_minus_iff (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) 1)). exact Ht1small. }
        assert (Hsh : ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                         - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))
                      - ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#3))
                      == ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6)
                            * (1 - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))))))
          by (unfold Qminus; ring).
        setoid_rewrite Hsh.
        exact Hpos. }
      apply (Qlt_le_trans d (eps0 * eps0 * (1#3))).
      + exact Hdlt.
      + apply (Qle_trans _ ((- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#2)
                            - (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (- u (Datatypes.S (Datatypes.S (Datatypes.S m)))) * (1#6))).
        * exact Hmid1.
        * exact HmidA. }
  (* δ 分支构造：1/(2C) < eps0²·⅓ 时取 δ := 1/(2C)，否则 δ := eps0²·⅙（留半间隙保严格） *)
  destruct (Qlt_le_dec (1 / (2 * C)) (eps0 * eps0 * (1#3))) as [Hmin | Hmin].
  - exists (1 / (2 * C)).
    split.
    + apply Qlt_to_QltT. exact HinvC.
    + exists (Nat.max N0 (2 * m0 + 3))%nat.
      intros n Hn.
      apply Hmain.
      * apply Qle_refl.
      * exact Hmin.
      * exact (NatLe_drop _ _ Hn).
  - exists (eps0 * eps0 * (1#6)).
    split.
    + apply Qlt_to_QltT. exact Hsixth.
    + exists (Nat.max N0 (2 * m0 + 3))%nat.
      intros n Hn.
      apply Hmain.
      * apply (Qle_trans _ (eps0 * eps0 * (1#3))).
        -- apply (Qlt_le_weak _ _). exact Hdstrict.
        -- exact Hmin.
      * exact Hdstrict.
      * exact (NatLe_drop _ _ Hn).
Qed.

(* ============================================================ *)
(* Part E：对数上切线 x<1 侧（Real 层）                                 *)
(*   0 < x < 1 ⟹ log x < x − 1                                          *)
(* ============================================================ *)

Lemma klst_log_tangent_neg : forall (x : Real)
  (Hx : real_lt real_zero x) (Hx1 : real_lt x real_one),
  real_lt (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx Hx1.
  assert (Hlogneg : real_lt (real_log x Hx) real_zero).
  { apply (RealSetoid.real_lt_id_r (real_log x Hx)
             (real_log real_one real_lt_zero_one) real_zero).
    - exact (real_log_one real_lt_zero_one).
    - exact (real_log_lt_mono x real_one Hx real_lt_zero_one Hx1). }
  assert (Htan : real_lt (real_plus real_one (real_log x Hx)) (cauchy_real_exp (real_log x Hx)))
    by exact (klst_exp_tangent_neg (real_log x Hx) Hlogneg).
  assert (Hval : real_eq (cauchy_real_exp (real_log x Hx)) x)
    by exact (cw_log_exp_right x Hx).
  assert (H2 : real_lt (real_plus real_one (real_log x Hx)) x)
    by exact (RealSetoid.real_lt_compat (real_plus real_one (real_log x Hx))
                                        (real_plus real_one (real_log x Hx))
                                        (cauchy_real_exp (real_log x Hx)) x
                                        (real_eq_refl (real_plus real_one (real_log x Hx)))
                                        Hval Htan).
  apply (RealSetoid.real_lt_id_l (real_log x Hx)
               (real_plus (real_opp real_one) (real_plus real_one (real_log x Hx)))
               (real_plus x (real_opp real_one))).
  + apply real_eq_sym.
    apply (real_eq_trans _ (real_plus (real_plus (real_opp real_one) real_one) (real_log x Hx)) _).
    * apply real_plus_assoc.
    * apply (real_eq_trans _ (real_plus real_zero (real_log x Hx)) _).
      -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp real_one) real_one)
                                              (real_log x Hx)
                                              real_zero (real_log x Hx)).
         ++ apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
            ** apply real_plus_comm.
            ** apply real_plus_opp.
         ++ apply real_eq_refl.
      -- apply (real_eq_trans _ (real_plus (real_log x Hx) real_zero) _).
         ++ apply real_plus_comm.
         ++ apply real_plus_zero.
  + apply (RealSetoid.real_lt_id_r
             (real_plus (real_opp real_one) (real_plus real_one (real_log x Hx)))
             (real_plus (real_opp real_one) x)
             (real_plus x (real_opp real_one))).
    * exact (real_plus_comm (real_opp real_one) x).
    * apply (real_lt_plus_translate (real_opp real_one)
                                    (real_plus real_one (real_log x Hx)) x).
      exact H2.
Qed.

(* ============================================================ *)
(* Part F：严格 Gibbs 逐点核 q<p 支（与 klst_gibbs_core_strict 成对）    *)
(* ============================================================ *)

Lemma klst_gibbs_core_strict_neg : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hqp : real_lt q p),
  real_lt real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hqp.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  assert (Hxpos : real_lt real_zero X) by exact HX.
  assert (Hx1 : real_lt X real_one).
  { apply (RealSetoid.real_lt_id_r X (real_mult p (real_inv_pos p Hp)) real_one).
    - exact (real_inv_pos_correct p Hp).
    - exact (real_mult_lt_compat q p (real_inv_pos p Hp) Hqp (real_inv_pos_pos p Hp)). }
  assert (Htan : real_lt L (real_plus X (real_opp real_one)))
    by exact (klst_log_tangent_neg X HX Hx1).
  assert (Hgap : real_lt real_zero (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (real_opp L) (real_plus X (real_opp real_one)))
             (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
    - apply real_plus_comm.
    - apply (RealSetoid.real_lt_id_l real_zero
               (real_plus (real_opp L) L)
               (real_plus (real_opp L) (real_plus X (real_opp real_one)))).
      + apply real_eq_sym.
        apply (real_eq_trans _ (real_plus L (real_opp L)) _).
        * apply real_plus_comm.
        * apply real_plus_opp.
      + exact (real_lt_plus_translate (real_opp L) L (real_plus X (real_opp real_one)) Htan). }
  assert (Hprod : real_lt real_zero (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L))))
    by exact (real_mult_pos_compat p
                (real_plus (real_plus X (real_opp real_one)) (real_opp L))
                Hp Hgap).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_mult p (real_plus (real_plus X (real_opp real_one)) (real_opp L)))
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
  - exact Hprod.
Qed.

(* ============================================================ *)
(* Part G：KL 严格和无条件主件（逐项前提换全称双向弱序）                 *)
(* ============================================================ *)

(* KL>0 无条件主件：双归一化 + 逐项双向可比（全称弱序：p≤q ∨ q≤p）+
   s₀ 处严格分离（任一方向 Or；能量非常数的比率分离见证）
   ⟹ 0 < Σ_s kl_term（表 l₁++s₀::l₂）。
   相对 UpReqKLStrict.klst_kl_sum_strict：逐项前提 real_le (p s) (q s)
   换为全称双向弱序 Or (real_le (p s) (q s)) (real_le (q s) (p s))，
   q>p 支由 klst_gibbs_core_strict_neg 补齐；s₀ 严格分离亦换双向 Or，
   温度桥两向均入。 *)
Lemma klst_kl_energy_nonconst : forall (X : Type) (l₁ : list X) (s₀ : X) (l₂ : list X)
  (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (Hpq : forall s : X, Or (real_le (p s) (q s)) (real_le (q s) (p s)))
  (Hnormp : real_eq (real_list_sum X p (l₁ ++ s₀ :: l₂)) real_one)
  (Hnormq : real_eq (real_list_sum X q (l₁ ++ s₀ :: l₂)) real_one)
  (Hdiv : Or (real_lt (p s₀) (q s₀)) (real_lt (q s₀) (p s₀))),
  real_lt real_zero
    (real_list_sum X (fun s => real_kl_term (p s) (q s) (Hp s) (Hq s)) (l₁ ++ s₀ :: l₂)).
Proof.
  intros X l₁ s₀ l₂ p q Hp Hq Hpq Hnormp Hnormq Hdiv.
  set (L := l₁ ++ s₀ :: l₂).
  set (KL := fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s)).
  set (G := fun s : X => real_plus (KL s) (real_plus (q s) (real_opp (p s)))).
  (* 1. 逐项 g ≥ 0（全称双向弱序四支：p<q / p==q / q<p / q==p） *)
  assert (Hgnonneg : forall s : X, real_le real_zero (G s)).
  { intro s. unfold G. destruct (Hpq s) as [Hle | Hle'].
    - destruct Hle as [Hlt | Heq].
      + unfold real_le. left.
        exact (klst_gibbs_core_strict (p s) (q s) (Hp s) (Hq s) Hlt).
      + unfold real_le. right. apply real_eq_sym.
        exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s) Heq).
    - destruct Hle' as [Hlt | Heq].
      + unfold real_le. left.
        exact (klst_gibbs_core_strict_neg (p s) (q s) (Hp s) (Hq s) Hlt).
      + unfold real_le. right. apply real_eq_sym.
        exact (klst_gibbs_core_zero (p s) (q s) (Hp s) (Hq s)
                 (real_eq_sym (q s) (p s) Heq)). }
  (* 2. Σ kl L == Σ G L（归一化零和抵消，gibbs_inequality_eps 同款） *)
  assert (Hzero : real_eq (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L) real_zero).
  { apply (real_eq_trans _ (real_plus (real_list_sum X p L) (real_list_sum X (fun s => real_opp (q s)) L)) _).
    - apply (real_list_sum_add X p (fun s => real_opp (q s)) L).
    - apply (real_eq_trans _ (real_plus real_one (real_opp real_one)) _).
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X p L)
                                             (real_list_sum X (fun s => real_opp (q s)) L)
                                             real_one (real_opp real_one)).
        * exact Hnormp.
        * apply (real_eq_trans _ (real_opp (real_list_sum X q L)) _).
          -- apply (real_list_sum_opp X q L).
          -- apply (RealSetoid.real_eq_opp_compat (real_list_sum X q L) real_one).
             exact Hnormq.
      + apply real_plus_opp. }
  assert (Hqp : real_eq (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L) real_zero).
  { apply (real_eq_trans _ (real_list_sum X (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L) _).
    - apply (real_list_sum_ext X (fun s => real_plus (q s) (real_opp (p s)))
                               (fun s => real_opp (real_plus (p s) (real_opp (q s)))) L).
      intro s. exact (klst_r_opp_minus (p s) (q s)).
    - apply (real_eq_trans _ (real_opp (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)) _).
      + apply (real_list_sum_opp X (fun s => real_plus (p s) (real_opp (q s))) L).
      + apply (real_eq_trans _ (real_opp real_zero) _).
        * apply (RealSetoid.real_eq_opp_compat (real_list_sum X (fun s => real_plus (p s) (real_opp (q s))) L)
                                               real_zero).
          exact Hzero.
        * exact real_opp_zero. }
  assert (HsumG : real_eq (real_list_sum X KL L) (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_list_sum X KL L)
                          (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)) _).
    - apply (real_eq_trans _ (real_plus (real_list_sum X KL L) real_zero) _).
      + apply real_eq_sym. apply real_plus_zero.
      + apply (RealSetoid.real_eq_plus_compat (real_list_sum X KL L) real_zero
                                              (real_list_sum X KL L)
                                              (real_list_sum X (fun s => real_plus (q s) (real_opp (p s))) L)).
        * apply real_eq_refl.
        * apply real_eq_sym. exact Hqp.
    - apply (real_eq_sym _ _). unfold G.
      apply (real_list_sum_add X KL (fun s => real_plus (q s) (real_opp (p s))) L). }
  (* 3. Σ G L == G s₀ + Σ G l₁ + Σ G l₂（app 拆分 + assoc + comm） *)
  assert (Hsplit : real_eq (real_list_sum X G L)
                           (real_plus (real_plus (G s₀) (real_list_sum X G l₁))
                                      (real_list_sum X G l₂))).
  { unfold L.
    apply (real_eq_trans _ (real_plus (real_list_sum X G l₁)
                                      (real_plus (G s₀) (real_list_sum X G l₂))) _).
    - exact (klst_list_sum_app X G l₁ (s₀ :: l₂)).
    - apply (real_eq_trans
               _ (real_plus (real_plus (real_list_sum X G l₁) (G s₀)) (real_list_sum X G l₂)) _).
      + apply real_plus_assoc.
      + apply (RealSetoid.real_eq_plus_compat (real_plus (real_list_sum X G l₁) (G s₀))
                                             (real_list_sum X G l₂)
                                             (real_plus (G s₀) (real_list_sum X G l₁))
                                             (real_list_sum X G l₂)).
        * apply real_plus_comm.
        * apply real_eq_refl. }
  (* 4. 尾和 ≥ 0 + 严格项 ⟹ 0 < Σ G L ⟹ 0 < Σ kl L *)
  assert (Htail : real_le real_zero (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
  { apply (RealSetoid.real_le_id_r real_zero (real_list_sum X G (l₁ ++ l₂))
                                   (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - exact (klst_list_sum_app X G l₁ l₂).
    - exact (real_list_sum_nonneg X G (l₁ ++ l₂) Hgnonneg). }
  assert (Hmain : real_lt real_zero (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))).
  { apply (klst_r_lt_plus_le (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂))).
    - unfold G. unfold KL. destruct Hdiv as [Hd | Hd].
      + exact (klst_gibbs_core_strict (p s₀) (q s₀) (Hp s₀) (Hq s₀) Hd).
      + exact (klst_gibbs_core_strict_neg (p s₀) (q s₀) (Hp s₀) (Hq s₀) Hd).
    - exact Htail. }
  assert (Hfin : real_eq (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
                         (real_list_sum X G L)).
  { apply (real_eq_trans
             _ (real_plus (real_plus (G s₀) (real_list_sum X G l₁)) (real_list_sum X G l₂)) _).
    - apply real_plus_assoc.
    - apply real_eq_sym. exact Hsplit. }
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (G s₀) (real_plus (real_list_sum X G l₁) (real_list_sum X G l₂)))
           (real_list_sum X KL L)).
  - apply (real_eq_trans _ (real_list_sum X G L) _).
    + exact Hfin.
    + apply real_eq_sym. exact HsumG.
  - exact Hmain.
Qed.

(* ============================================================ *)
(* 闭合证明（Print Assumptions 须全 Closed）                            *)
(* ============================================================ *)

Print Assumptions klst_q_pair_nonneg.
Print Assumptions klst_q_pow_pos.
Print Assumptions klst_q_pow_neg_even.
Print Assumptions klst_q_pow_neg_odd.
Print Assumptions klst_q_pow_neg_odd_lt.
Print Assumptions klst_q_lt0_opp.
Print Assumptions klst_q_div_lt0.
Print Assumptions klst_ep_four_terms_odd.
Print Assumptions klst_ep_four_terms_even.
Print Assumptions klst_ep_four_terms.
Print Assumptions klst_exp_tangent_neg.
Print Assumptions klst_log_tangent_neg.
Print Assumptions klst_gibbs_core_strict_neg.
Print Assumptions klst_kl_energy_nonconst.

(* ============================================================ *)
(* 尾注（判词台账）                                                    *)
(*   判词 A（缺口单引理闭合）：Q 层四项交错部分和下界                       *)
(*     1−t+t²/2−t³/6 ≤ ep_n(−t) 对 0≤t≤1、n≥3 全体成立（klst_ep_four_terms）。 *)
(*     截断方向裁决：exp_partial n x 定义为前 n+1 项部分和（k=0..n），     *)
(*     负 argument 交错级数下侧截断取 S₃（奇号三项截断）；n=3 处          *)
(*     exp_partial 3 (−t) ≡ S₃ 恒等式入场，奇号子列经配对项              *)
(*     t^{2k}/(2k)! − t^{2k+1}/(2k+1)! ≥ 0（klst_q_pair_nonneg，          *)
(*     q_pair2_nonneg 的一般指数版）两步单调升，偶号项 = 奇号前项 +       *)
(*     正尾项 t^{2j+4}/(2j+4)! ≥ 0。Witness：n := 3+m 构造性给出。        *)
(*   判词 B（负支切线）：w<0 ⟹ 1+w<e^w 的分离见证 δ 分支构造——           *)
(*     t := −u_n > 1 支的偶号下界不随 t−1 一致（t→1⁺ 时失效），改经       *)
(*     「奇号项 = 偶号项 + 负尾商」传递 exp_partial_odd_lower 的          *)
(*     1/(2C) 正下界（M/C/m0 供给链同 real_exp_ge_linear_eps）；          *)
(*     t ≤ 1 支由缺口单引理给 ≥ t²(3−t)/6 ≥ t²/3 ≥ eps0²/3。             *)
(*     δ 取 min 的两支：eps0²/3 ≤ 1/(2C) 时 δ := eps0²/6（留半间隙        *)
(*     保 QltT 严格性），否则 δ := 1/(2C)。                              *)
(*   判词 C（无条件主件形状）：逐项 real_le real_zero (G s)（Or 形）       *)
(*     对任意 p,q 不可构造（等号点不可判定），全称弱序 comparability      *)
(*     （p≤q ∨ q≤p）必须以前提承载——Gibbs 两温度族满足之（比率单调，     *)
(*     具体实例经 cauchy_real_exp_mono 严格单调消解）；s₀ 严格分离同理    *)
(*     以双向 Or 前提承载。逐项 Bishop 形（eps 余量）无前提路线由库侧     *)
(*     real_gibbs_core_eps / real_gibbs_inequality_eps 承载，其严格化     *)
(*     收口器（real_le_b 系）留待后续席位。                              *)
(* ============================================================ *)
