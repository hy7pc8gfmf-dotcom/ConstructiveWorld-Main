(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   rtb_rlt_eq_r（原 L304，3 句玩具证）                                  *)
(*   rtb_rlt_eq_l（原 L296，3 句玩具证）                                  *)
(*   rtb_neq_of_ltT（原 L109，4 句玩具证）                                *)
(*   rtb_qleT_mult_r（原 L83，3 句玩具证）                                *)
(*   rtb_qleT_refl（原 L60，3 句玩具证）                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqRatioTail.v —— 比值型几何尾界母定理（一母多子实例化）         *)
(*                                                              *)
(* 目的：把 exp/arctan 等级数证明里反复内联的「比值受控 ⟹ 尾和        *)
(*   被首项封顶」论证粗粒化为母定理，一处证成、多点实例化。            *)
(*                                                              *)
(* 主件（前缀 rtb_，避免与库内既有名冲突）：                         *)
(*   Part 1  Q 层工具：rtb_qleT_refl/_trans/_mult_l/_mult_r、        *)
(*           rtb_qle_0_minus、rtb_zpos_S、rtb_qleT_div_r、            *)
(*           rtb_qlt_0_minus、rtb_neq_of_ltT、rtb_one_minus_neq、      *)
(*           rtb_pow_le_one。                                        *)
(*   Part 2  Q 层母引理：rtb_tsum（有限和定义）＋                     *)
(*           rtb_ratio_tail_Q_mult（乘形式，telescoping＋Q 环账）      *)
(*           ＋ rtb_ratio_tail_Q（除形式 ≤ u_n·(1−ρ^N)/(1−ρ)，          *)
(*           承 Qmult_le_r）。                                        *)
(*   Part 3  Real 层母定理：rtb_rsum ＋ 逐点/序工具                    *)
(*           （rtb_rc_* 环账、rtb_rlt_eq_l/r、rtb_rlt_plus_l/r、       *)
(*           rtb_rplus_le_compat、rtb_rmult_le_compat_l/r、            *)
(*           rtb_step_le、rtb_c_nonneg）＋                             *)
(*           rtb_ratio_tail_real（Bishop/eps 形）。                    *)
(*   Part 4  两实例（真走母定理，非平行抄写）：                        *)
(*           exp 位点：rtb_exp_ratio → rtb_exp_inst（Q）＋              *)
(*                     rtb_exp_real_inst（Real 消费 rtb_ratio_tail_real）； *)
(*           arctan 位点：rtb_atan_ratio → rtb_atan_cert（指标平移）    *)
(*                     → rtb_atan_inst（Q，真走母定理，以 rtb_tsum      *)
(*                     直陈式收口，无垫片）。                           *)
(*                                                              *)
(* 供体位点（全部只读消费，未改任何既有文件）：                        *)
(*   S03_QExp.v:622 exp_tail_abs_geom2 系（q_pow/q_fact/               *)
(*   q_pow_nonneg/q_fact_pos/q_fact_succ/q_neq_of_lt 供 Q 环账）；      *)
(*   S11_TP3B5.v:137 atan_mag_succ_geom 系（atan_q_pow_odd3/            *)
(*   atan_odd_pos/atan_sq_abs/arctan_term_abs 供 arctan 位点）。        *)
(*   参照（未 Require 未改）：待入库稿 ArctanGeomTail.v                 *)
(*   atg_tail_geom:278——其 Leibniz 成对收紧 c_{m+1} 强于本件纯比值      *)
(*   形 c_{m+1}/(1−r)，两路线强弱关系如上记档。                         *)
(*                                                              *)
(* 备注：公理面零新增公理；全部前提为 Set 层显式证书                    *)
(*   （QleT'/QltT = Id 判定器值、real_lt = eps 见证 sigT、real_le =     *)
(*   Or 编码）；文末 Print Assumptions 预期全 Closed。                  *)
(*   语句面全 Set 层（量词 nat/Q/nat->Q/nat->Real/Real；比较全          *)
(*   QleT'/QltT/real_lt/real_le/real_eq）；签名零 Prop 泄露；           *)
(*   零经典逻辑（Qeq_dec/Qle_lt_or_eq 均为可计算判定器）；              *)
(*   证明内 Prop 分支仅证明性分情况消解，产物全 Set。                   *)
(*   数值前置校核：母引理常数经精确有理数算术对 12 组 (ρ,n,N) 采样      *)
(*   验算全过（几何恒等式精确成立＋递推 c_{SN'}=1+ρ·c_{N'}）。           *)
(* ============================================================ *)
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1：Q 层工具                                                 *)
(* ============================================================ *)

Lemma rtb_qleT_refl : forall a : Q, QleT' a a.
Proof. intro a. apply Qle_to_QleT'. apply Qle_refl. Qed.

Lemma rtb_qleT_trans : forall a b c : Q, QleT' a b -> QleT' b c -> QleT' a c.
Proof.
  intros a b c Hab Hbc. apply Qle_to_QleT'.
  apply (Qle_trans a b c).
  - apply QleT'_to_Qle. exact Hab.
  - apply QleT'_to_Qle. exact Hbc.
Qed.

(* 左乘正（非负）常数的 QleT' 单调 *)
Lemma rtb_qleT_mult_l : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (c * a) (c * b).
Proof.
  intros a b c Hab Hc. apply Qle_to_QleT'.
  assert (Hb : Qle a b) by (apply QleT'_to_Qle; exact Hab).
  assert (Hc' : Qle 0 c) by (apply QleT'_to_Qle; exact Hc).
  pose proof (Qmult_le_compat_r a b c Hb Hc') as H.
  rewrite (Qmult_comm c a). rewrite (Qmult_comm c b). exact H.
Qed.

(* 右乘非负常数的 QleT' 单调 *)
Lemma rtb_qleT_mult_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc.
  apply Qle_to_QleT'.
  apply Qmult_le_compat_r;    [apply QleT'_to_Qle; exact Hab | apply QleT'_to_Qle; exact Hc].
Qed.

(* ρ ≤ 1 ⟹ 0 ≤ 1-ρ（Qopp_le_compat 反向 + 环账） *)
Lemma rtb_qle_0_minus : forall rho : Q, QleT' rho 1 -> QleT' 0 (1 - rho).
Proof.
  intros rho H. apply Qle_to_QleT'. apply QleT'_to_Qle in H.
  apply (Qle_trans _ ((- 1) + 1)%Q).
  - apply qeq_le. ring.
  - apply (Qle_trans _ ((- rho) + 1)%Q).
    + apply Qplus_le_compat.
      * apply (Qopp_le_compat rho 1 H).
      * apply Qle_refl.
    + apply qeq_le. ring.
Qed.

(* S n 型正整数分母正性（承 S03 q_fact_pos 同款） *)
Lemma rtb_zpos_S : forall n : nat, QltT 0 (Z.of_nat (Datatypes.S n) # 1).
Proof. intro n. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* 正非零 *)
Lemma rtb_neq_of_ltT : forall q : Q, QltT 0 q -> ~ (q == 0).
Proof. intros q H. apply q_neq_of_lt. apply QltT_to_Qlt. exact H. Qed.

(* 除法保序（正分母）：a ≤T b ⟹ a/K ≤T b/K（承 Qmult_le_r） *)
Lemma rtb_qleT_div_r : forall a b K : Q,
  QleT' a b -> QltT 0 K -> QleT' (a / K) (b / K).
Proof.
  intros a b K Hab HK. apply Qle_to_QleT'.
  assert (HK' : Qlt 0 K) by (apply QltT_to_Qlt; exact HK).
  assert (HKnz : ~ (K == 0)) by (apply rtb_neq_of_ltT; exact HK).
  apply (proj1 (Qmult_le_r (a / K) (b / K) K HK')).
  apply (Qle_trans _ a).
  - apply qeq_le. field. exact HKnz.
  - apply (Qle_trans _ b).
    + apply QleT'_to_Qle. exact Hab.
    + apply qeq_le. field. exact HKnz.
Qed.

(* 严格减：a < b ⟹ 0 < b - a（承 Qplus_lt_r） *)
Lemma rtb_qlt_0_minus : forall a b : Q, Qlt a b -> Qlt 0 (b - a).
Proof.
  intros a b H.
  pose proof (proj2 (Qplus_lt_r a b (- a)) H) as Ht.
  assert (E1 : ((- a) + a)%Q == 0) by field.
  assert (E2 : ((- a) + b)%Q == (b - a)) by field.
  setoid_rewrite E1 in Ht. setoid_rewrite E2 in Ht. exact Ht.
Qed.

(* ρ < 1 ⟹ 1-ρ ≠ 0 *)
Lemma rtb_one_minus_neq : forall rho : Q, QltT rho 1 -> ~ ((1 - rho) == 0).
Proof.
  intros rho H1 Hz.
  assert (Hr : rho == 1).
  { assert (Er : rho == (1 - (1 - rho))%Q) by ring.
    rewrite Er. rewrite Hz. ring. }
  apply (Qlt_not_eq rho 1 (QltT_to_Qlt rho 1 H1)). exact Hr.
Qed.

(* ρ^n ≤ 1（0 ≤ ρ ≤ 1） *)
Lemma rtb_pow_le_one : forall (rho : Q) (n : nat),
  QleT' 0 rho -> QleT' rho 1 -> QleT' (q_pow rho n) 1.
Proof.
  intros rho n H0 H1. induction n as [| n IH].
  - apply Qle_to_QleT'. change (q_pow rho 0%nat) with 1%Q. apply Qle_refl.
  - change (q_pow rho (Datatypes.S n)) with (rho * q_pow rho n).
    apply (rtb_qleT_trans _ (1 * q_pow rho n)).
    + apply rtb_qleT_mult_r;
        [exact H1 | apply Qle_to_QleT'; apply q_pow_nonneg; apply QleT'_to_Qle; exact H0].
    + apply (rtb_qleT_trans _ (1 * 1)%Q).
      * apply rtb_qleT_mult_l; [exact IH | apply Qle_to_QleT'; exact Qle_0_1].
      * apply qeq_leT'. ring.
Qed.

(* ============================================================ *)
(* Part 2：母引理（Q 层）——比值证书 ⟹ 有限和被首项几何封顶        *)
(* ============================================================ *)

(* 有限和：Σ_{k=0}^{N-1} u (n+k) *)
Fixpoint rtb_tsum (u : nat -> Q) (n N : nat) : Q :=
  match N with
  | O => 0
  | Datatypes.S N' => u n + rtb_tsum u (Datatypes.S n) N'
  end.

(* 追加引理：S d 项和 == d 项和 + 末项（供位点垫片对齐消费形） *)
Lemma rtb_tsum_S : forall (u : nat -> Q) (n d : nat),
  rtb_tsum u n (Datatypes.S d) == rtb_tsum u n d + u (n + d)%nat.
Proof.
  intros u n d. revert n. induction d as [| d IH]; intro n.
  - change (rtb_tsum u n 1%nat) with (u n + rtb_tsum u (Datatypes.S n) 0%nat).
    change (rtb_tsum u (Datatypes.S n) 0%nat) with 0%Q.
    change (rtb_tsum u n 0%nat) with 0%Q.
    replace (n + 0)%nat with n by lia. ring.
  - change (rtb_tsum u n (Datatypes.S (Datatypes.S d)))
      with (u n + rtb_tsum u (Datatypes.S n) (Datatypes.S d)).
    change (rtb_tsum u n (Datatypes.S d))
      with (u n + rtb_tsum u (Datatypes.S n) d).
    rewrite (IH (Datatypes.S n)).
    replace (Datatypes.S n + d)%nat with (n + Datatypes.S d)%nat by lia.
    ring.
Qed.

(* 母引理核心：乘形式（telescoping + Q 环账，对任意变号 u 成立） *)
Lemma rtb_ratio_tail_Q_mult : forall (u : nat -> Q) (rho : Q) (N n : nat),
  QleT' 0 rho -> QltT rho 1 ->
  (forall j : nat, QleT' (u (Datatypes.S j)) (rho * u j)) ->
  QleT' (rtb_tsum u n N * (1 - rho)) (u n * (1 - q_pow rho N)).
Proof.
  intros u rho N. induction N as [| N' IH]; intros n H0 H1 Hcert.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ 0%Q).
    + apply qeq_le. change (rtb_tsum u n 0%nat) with 0%Q. ring.
    + apply qeq_le. change (q_pow rho 0%nat) with 1%Q. ring.
  - assert (Hr1 : QleT' rho 1)
      by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact H1).
    assert (Hle0 : QleT' 0 (1 - rho)) by (apply rtb_qle_0_minus; exact Hr1).
    specialize (IH (Datatypes.S n) H0 H1 Hcert).
    apply Qle_to_QleT'.
    change (q_pow rho (Datatypes.S N')) with (rho * q_pow rho N').
    change (rtb_tsum u n (Datatypes.S N'))
      with (u n + rtb_tsum u (Datatypes.S n) N').
    apply (Qle_trans _ (u n * (1 - rho) + rtb_tsum u (Datatypes.S n) N' * (1 - rho))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ (u n * (1 - rho) + u (Datatypes.S n) * (1 - q_pow rho N'))).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact (QleT'_to_Qle _ _ IH).
      * apply (Qle_trans _ (u n * (1 - rho) + (rho * u n) * (1 - q_pow rho N'))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qmult_le_compat_r;
                [apply QleT'_to_Qle; apply Hcert
                | exact (QleT'_to_Qle _ _
                           (rtb_qle_0_minus (q_pow rho N')
                              (rtb_pow_le_one rho N' H0 Hr1)))].
        -- apply qeq_le. ring.
Qed.

(* 母引理（除形式）：Σ_{k<N} u_{n+k} ≤ u_n·(1-ρ^N)/(1-ρ) *)
Lemma rtb_ratio_tail_Q : forall (u : nat -> Q) (rho : Q) (N n : nat),
  QleT' 0 rho -> QltT rho 1 ->
  (forall j : nat, QleT' (u (Datatypes.S j)) (rho * u j)) ->
  QleT' (rtb_tsum u n N) (u n * ((1 - q_pow rho N) / (1 - rho))).
Proof.
  intros u rho N n H0 H1 Hcert.
  pose proof (rtb_ratio_tail_Q_mult u rho N n H0 H1 Hcert) as Hm.
  assert (Hle0 : Qle 0 (1 - rho)).
  { apply QleT'_to_Qle. apply rtb_qle_0_minus.
    apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact H1. }
  assert (Hnz : ~ ((1 - rho) == 0)) by (apply rtb_one_minus_neq; exact H1).
  assert (Hlt0 : Qlt 0 (1 - rho)).
  { destruct (Qle_lt_or_eq 0 (1 - rho) Hle0) as [Hlt | Heq].
    - exact Hlt.
    - exfalso. apply Hnz. apply Qeq_sym. exact Heq. }
  apply Qle_to_QleT'.
  apply (proj1 (Qmult_le_r (rtb_tsum u n N)
             (u n * ((1 - q_pow rho N) / (1 - rho))) (1 - rho)%Q Hlt0)).
  apply (Qle_trans _ (u n * (1 - q_pow rho N))).
  - exact (QleT'_to_Qle _ _ Hm).
  - apply qeq_le. field. exact Hnz.
Qed.

(* ============================================================ *)
(* Part 3：母定理（Real 层，Bishop/eps 形）                       *)
(* ============================================================ *)

(* Real 有限和：Σ_{k<N} u (n+k) *)
Fixpoint rtb_rsum (u : nat -> Real) (n N : nat) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S N' => real_plus (u n) (rtb_rsum u (Datatypes.S n) N')
  end.

(* 逐点环账 tactic（承 UpReqMixingTime mix_rring / UpTVDoeblin tvd_rring 口径） *)
Ltac rtb_rproj_ring :=
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_const real_of_nat] in *;
  ring.

(* real_const 环账族（全自含量化，destruct 安全） *)
Lemma rtb_rc_wd : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_const]. rewrite H. ring.
Qed.

Lemma rtb_rc_mult0_plus : forall (x e : Real),
  real_eq (real_plus (real_mult x (real_const 0)) e) e.
Proof. intros x e. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

Lemma rtb_rc_mult_comm : forall (x : Real) (a : Q),
  real_eq (real_mult x (real_const a)) (real_mult (real_const a) x).
Proof. intros x a. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

Lemma rtb_rc_plus_comm : forall x y : Real,
  real_eq (real_plus x y) (real_plus y x).
Proof. intros x y. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

Lemma rtb_rc_step_eq : forall (x e : Real) (a b : Q),
  real_eq (real_plus x (real_plus (real_mult (real_mult (real_const a) x) (real_const b)) e))
          (real_plus (real_mult x (real_const (1 + a * b))) e).
Proof. intros x e a b. apply real_eq_of_zero_diff. intro n0. rtb_rproj_ring. Qed.

(* lt 在 real_eq 下的双向搬移（承 real_le_lt_trans/real_lt_le_trans） *)
Lemma rtb_rlt_eq_l : forall x y z : Real,
  real_eq x y -> real_lt z x -> real_lt z y.
Proof.
  intros x y z Hxy Hlt.
  apply (real_lt_le_trans z x y Hlt).
  apply (RealSetoid.real_eq_le x y Hxy).
Qed.

Lemma rtb_rlt_eq_r : forall x y z : Real,
  real_eq y z -> real_lt x y -> real_lt x z.
Proof.
  intros x y z Hyz Hlt.
  apply (real_lt_le_trans x y z Hlt).
  apply (RealSetoid.real_eq_le y z Hyz).
Qed.

(* 加法右/左平移保 lt *)
Lemma rtb_rlt_plus_r : forall a b c : Real,
  real_lt a b -> real_lt (real_plus a c) (real_plus b c).
Proof.
  intros a b c Hlt. destruct Hlt as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn. specialize (HN n Hn).
    destruct a as [ua Ha]; destruct b as [ub Hb]; destruct c as [uc Hc].
    cbn [projT1 real_plus] in *.
    pose proof (QltT_to_Qlt e (ub n - ua n) HN) as HN'.
    apply Qlt_to_QltT.
    assert (E : ub n + uc n - (ua n + uc n) == ub n - ua n) by ring.
    setoid_rewrite E. exact HN'.
Qed.

Lemma rtb_rlt_plus_l : forall a b c : Real,
  real_lt a b -> real_lt (real_plus c a) (real_plus c b).
Proof.
  intros a b c Hlt. destruct Hlt as [e [He [N HN]]].
  exists e. split.
  - exact He.
  - exists N. intros n Hn. specialize (HN n Hn).
    destruct a as [ua Ha]; destruct b as [ub Hb]; destruct c as [uc Hc].
    cbn [projT1 real_plus] in *.
    pose proof (QltT_to_Qlt e (ub n - ua n) HN) as HN'.
    apply Qlt_to_QltT.
    assert (E : uc n + ub n - (uc n + ua n) == ub n - ua n) by ring.
    setoid_rewrite E. exact HN'.
Qed.

(* 加法双单调（real_le） *)
Lemma rtb_rplus_le_compat : forall a b c d : Real,
  real_le a b -> real_le c d -> real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct Hab as [Hltab | Heqab]; destruct Hcd as [Hltcd | Heqcd].
  - left. apply real_lt_plus_compat.
    + exact Hltab.
    + exact Hltcd.
  - left.
    apply (rtb_rlt_eq_r _ _ _
             (RealSetoid.real_eq_plus_compat b c b d (real_eq_refl b) Heqcd)).
    apply rtb_rlt_plus_r. exact Hltab.
  - left.
    apply (rtb_rlt_eq_r _ (real_plus d a) _
             (real_eq_trans (real_plus d a) (real_plus d b) (real_plus b d)
                (RealSetoid.real_eq_plus_compat d a d b (real_eq_refl d) Heqab)
                (rtb_rc_plus_comm d b))).
    apply (real_le_lt_trans _ (real_plus c a) (real_plus d a)
             (RealSetoid.real_eq_le _ _ (rtb_rc_plus_comm a c))).
    apply rtb_rlt_plus_r. exact Hltcd.
  - right. apply (RealSetoid.real_eq_plus_compat a c b d Heqab Heqcd).
Qed.

(* 左乘 Q 常数的 real_le 单调（非平凡：0 支归 eq，正支 eps 缩放逐点） *)
Lemma rtb_rmult_le_compat_l : forall (x y : Real) (c : Q),
  real_le x y -> QleT' 0 c ->
  real_le (real_mult (real_const c) x) (real_mult (real_const c) y).
Proof.
  intros x y c Hle Hc0. destruct Hle as [Hlt | Heq].
  - destruct (Qeq_dec c 0) as [Hc | Hc].
    + right.
      apply (real_eq_trans (real_mult (real_const c) x) real_zero
                           (real_mult (real_const c) y)).
      * apply real_eq_of_zero_diff. intro n0.
        destruct x; destruct y; cbn [projT1 real_mult real_const real_zero] in *;
          rewrite Hc; ring.
      * apply real_eq_sym. apply real_eq_of_zero_diff. intro n0.
        destruct x; destruct y; cbn [projT1 real_mult real_const real_zero] in *;
          rewrite Hc; ring.
    + left.
      assert (Hcpos : Qlt 0 c).
      { destruct (Qle_lt_or_eq 0 c (QleT'_to_Qle 0 c Hc0)) as [Hlt0 | Heq0].
        - exact Hlt0.
        - exfalso. apply Hc. apply Qeq_sym. exact Heq0. }
      destruct Hlt as [e [He [N HN]]].
      assert (Hepos : Qlt 0 e) by (apply QltT_to_Qlt; exact He).
      exists (c * e)%Q. split.
      * apply Qlt_to_QltT. apply (Qmult_lt_0_compat c e Hcpos Hepos).
      * exists N. intros n Hn. specialize (HN n Hn).
        destruct x as [vx Hvx]; destruct y as [vy Hvy].
        cbn [projT1 real_mult real_const real_zero] in *.
        pose proof (QltT_to_Qlt e (vy n - vx n) HN) as HN'.
        apply Qlt_to_QltT.
        assert (E : c * vy n - c * vx n == c * (vy n - vx n)) by ring.
        setoid_rewrite E.
        pose proof (Qmult_lt_compat_r e (vy n - vx n) c Hcpos HN') as HC.
        rewrite <- (Qmult_comm c e) in HC.
        rewrite (Qmult_comm (vy n - vx n) c) in HC.
        exact HC.
  - right.
    apply (RealSetoid.real_eq_mult_compat (real_const c) x (real_const c) y
             (real_eq_refl (real_const c)) Heq).
Qed.

(* 右乘 Q 常数的 real_le 单调（恒等重排 + 左乘版） *)
Lemma rtb_rmult_le_compat_r : forall (x y : Real) (c : Q),
  real_le x y -> QleT' 0 c ->
  real_le (real_mult x (real_const c)) (real_mult y (real_const c)).
Proof.
  intros x y c Hle Hc0.
  apply (real_le_trans (real_mult x (real_const c))
           (real_mult (real_const c) y) (real_mult y (real_const c))).
  - apply (real_le_trans (real_mult x (real_const c))
             (real_mult (real_const c) x) (real_mult (real_const c) y)).
    + apply (RealSetoid.real_eq_le). apply (rtb_rc_mult_comm x c).
    + apply rtb_rmult_le_compat_l; assumption.
  - apply (RealSetoid.real_eq_le).
    exact (real_eq_sym (real_mult y (real_const c)) (real_mult (real_const c) y)
             (rtb_rc_mult_comm y c)).
Qed.

(* 递推常数恒等（field 账，供步例 rewrite） *)
Lemma rtb_c_rec : forall (rho : Q) (N : nat), ~ ((1 - rho) == 0) ->
  (1 - q_pow rho (Datatypes.S N)) / (1 - rho)
    == (1 + rho * ((1 - q_pow rho N) / (1 - rho)))%Q.
Proof.
  intros rho N Hnz. unfold Qdiv.
  change (q_pow rho (Datatypes.S N)) with (rho * q_pow rho N).
  field. intro Hzl. apply Hnz. rewrite Hzl. apply Qeq_refl.
Qed.

(* c_N ≥ 0（0 ≤ ρ < 1）：0/(1-ρ) ≤ (1-ρ^N)/(1-ρ) 承 div_r + pow_le_one *)
Lemma rtb_c_nonneg : forall (rho : Q) (N : nat),
  QleT' 0 rho -> QltT rho 1 -> QleT' 0 ((1 - q_pow rho N) / (1 - rho)).
Proof.
  intros rho N H0 H1.
  assert (Hr1 : QleT' rho 1)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact H1).
  assert (Hle01 : QleT' 0 (1 - rho)) by (apply rtb_qle_0_minus; exact Hr1).
  assert (Hle0q : Qle 0 (1 - rho)) by (apply QleT'_to_Qle; exact Hle01).
  assert (Hlt0 : Qlt 0 (1 - rho)).
  { destruct (Qle_lt_or_eq 0 (1 - rho) Hle0q) as [Hlt | Heq].
    - exact Hlt.
    - exfalso. apply (rtb_one_minus_neq rho H1). apply Qeq_sym. exact Heq. }
  apply (rtb_qleT_trans _ (0 / (1 - rho))).
  - apply qeq_leT'. unfold Qdiv. ring.
  - apply rtb_qleT_div_r.
    + apply rtb_qle_0_minus. apply rtb_pow_le_one; assumption.
    + apply Qlt_to_QltT. exact Hlt0.
Qed.

(* 步例右支独立化：u (S n)·cN + eps ≤ (ρ·u n)·cN + eps（单层，避免深嵌套） *)
Lemma rtb_step_le : forall (u : nat -> Real) (rho cN : Q) (n : nat) (eps : Real),
  real_le (u (Datatypes.S n)) (real_mult (real_const rho) (u n)) ->
  QleT' 0 cN ->
  real_le (real_plus (real_mult (u (Datatypes.S n)) (real_const cN)) eps)
          (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps).
Proof.
  intros u rho cN n eps Hcert HcN.
  apply rtb_rplus_le_compat.
  - apply rtb_rmult_le_compat_r; assumption.
  - apply real_le_refl.
Qed.

(* 母定理：比值证书 ⟹ 尾和 < u_n·(1-ρ^N)/(1-ρ) + eps（Bishop/eps 形） *)
Lemma rtb_ratio_tail_real : forall (u : nat -> Real) (rho : Q) (N n : nat),
  QleT' 0 rho -> QltT rho 1 ->
  (forall j : nat, real_le (u (Datatypes.S j)) (real_mult (real_const rho) (u j))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt (rtb_rsum u n N)
          (real_plus (real_mult (u n) (real_const ((1 - q_pow rho N) / (1 - rho)))) eps).
Proof.
  intros u rho N. induction N as [| N' IH]; intros n H0 H1 Hcert eps Heps.
  - (* 基例：尾和 0 < 0·u_n + eps *)
    assert (Hz : ((1 - 1) / (1 - rho))%Q == 0%Q)
      by (field; exact (rtb_one_minus_neq rho H1)).
    change (q_pow rho 0%nat) with 1%Q.
    assert (E0 : real_eq (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps) eps).
    { apply (real_eq_trans
               (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps)
               (real_plus (real_mult (u n) (real_const 0)) eps) eps).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps
                 (real_mult (u n) (real_const 0)) eps).
        + apply (RealSetoid.real_eq_mult_compat (u n)
                   (real_const ((1 - 1) / (1 - rho))%Q) (u n) (real_const 0)
                   (real_eq_refl (u n)) (rtb_rc_wd _ _ Hz)).
        + apply real_eq_refl.
      - exact (rtb_rc_mult0_plus (u n) eps). }
    apply (rtb_rlt_eq_r real_zero eps
             (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps)
             (real_eq_sym
                (real_plus (real_mult (u n) (real_const ((1 - 1) / (1 - rho))%Q)) eps)
                eps E0) Heps).
  - (* 步例：c_{S N'} == 1 + ρ·c_{N'} 递推 + 单步证书 *)
    assert (Hr1 : QleT' rho 1)
      by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact H1).
    specialize (IH (Datatypes.S n) H0 H1 Hcert eps Heps).
    set (cN := ((1 - q_pow rho N') / (1 - rho))%Q) in *.
    set (cS := ((1 - q_pow rho (Datatypes.S N')) / (1 - rho))%Q) in *.
    assert (Hrec : cS == (1 + rho * cN)%Q).
    { unfold cS, cN. apply rtb_c_rec. intro Hz. apply (rtb_one_minus_neq rho H1 Hz). }
    assert (Hstep_eq : real_eq
             (real_plus (u n) (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps))
             (real_plus (real_mult (u n) (real_const cS)) eps)).
    { apply (real_eq_trans
               (real_plus (u n) (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps))
               (real_plus (real_mult (u n) (real_const (1 + rho * cN))) eps)
               (real_plus (real_mult (u n) (real_const cS)) eps)).
      - apply rtb_rc_step_eq.
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult (u n) (real_const (1 + rho * cN))) eps
                 (real_mult (u n) (real_const cS)) eps).
        + apply (RealSetoid.real_eq_mult_compat (u n) (real_const (1 + rho * cN)) (u n) (real_const cS)
                   (real_eq_refl (u n)) (rtb_rc_wd (1 + rho * cN) cS (Qeq_sym _ _ Hrec))).
        + apply real_eq_refl. }
    apply (real_lt_le_trans
             _ (real_plus (u n)
                  (real_plus (real_mult (u (Datatypes.S n)) (real_const cN)) eps))).
    + apply rtb_rlt_plus_l. exact IH.
    + assert (Hcert' : real_le (u (Datatypes.S n))
                         (real_mult (real_const rho) (u n))) by (apply Hcert).
      apply (real_le_trans
               _ (real_plus (u n)
                    (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps))
               (real_plus (real_mult (u n) (real_const cS)) eps)).
      * apply (rtb_rplus_le_compat (u n) (u n)
                   (real_plus (real_mult (u (Datatypes.S n)) (real_const cN)) eps)
                   (real_plus (real_mult (real_mult (real_const rho) (u n)) (real_const cN)) eps));
          [apply real_le_refl
          | apply (rtb_step_le u rho cN n eps (Hcert n) (rtb_c_nonneg rho N' H0 H1))].
      * apply (RealSetoid.real_eq_le). exact Hstep_eq.
Qed.

(* Qle 沿 Qeq 的左右搬移（Prop 层，配合 qeq_le） *)
Lemma rtb_qle_eq_l : forall X Y Z : Q, X == Y -> Qle Y Z -> Qle X Z.
Proof.
  intros X Y Z Hxy Hyz. apply (Qle_trans X Y Z).
  - apply qeq_le. exact Hxy.
  - exact Hyz.
Qed.

Lemma rtb_qle_eq_r : forall X Y Z : Q, Qle X Y -> Y == Z -> Qle X Z.
Proof.
  intros X Y Z Hxy Hyz. apply (Qle_trans X Y Z).
  - exact Hxy.
  - apply qeq_le. exact Hyz.
Qed.

(* ============================================================ *)
(* Part 4a：exp 位点实例（真走母定理）                               *)
(* ============================================================ *)

(* exp 尾项族：u j := A^{S(m+j)}/(S(m+j))! *)
Definition rtb_exp_term (A : Q) (m j : nat) : Q :=
  q_pow A (Datatypes.S (m + j)%nat) / q_fact (Datatypes.S (m + j)%nat).

(* /-代数一步（field 收口，侧条件显式化） *)
Lemma rtb_field_test : forall X dd D : Q, 0 < dd -> 0 < D -> 0 < dd * D ->
  ((1 / 2) * (X * dd)) / (dd * D) == (1 / 2) * (X / D).
Proof.
  intros X dd D H1 H2 H3. unfold Qdiv. field.
  split.
  - exact (q_neq_of_lt D H2).
  - exact (q_neq_of_lt dd H1).
Qed.

(* 比值证书：u (S j) ≤ (1/2)·u j（由 S03 几何条件 2A ≤ t+1 于 t := m+j+1） *)
Lemma rtb_exp_ratio : forall (A : Q) (m j : nat),
  QleT' 0 A ->
  (forall t : nat, (m <= t)%nat -> QleT' ((1 + 1) * A) (Z.of_nat (t + 1)%nat # 1)) ->
  QleT' (rtb_exp_term A m (Datatypes.S j)) ((1 / 2) * rtb_exp_term A m j).
Proof.
  intros A m j HA Hgeom.
  unfold rtb_exp_term.
  replace (m + Datatypes.S j)%nat with (Datatypes.S (m + j)) by lia.
  set (k := (m + j)%nat).
  assert (Hpow : q_pow A (Datatypes.S (Datatypes.S k)) == A * q_pow A (Datatypes.S k))
    by reflexivity.
  assert (Hfact : q_fact (Datatypes.S (Datatypes.S k))
                  == (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k))
    by apply q_fact_succ.
  assert (Hm : (m <= Datatypes.S k)%nat) by (unfold k; lia).
  specialize (Hgeom (Datatypes.S k) Hm).
  replace (Datatypes.S k + 1)%nat with (Datatypes.S (Datatypes.S k)) in Hgeom by lia.
  assert (HX0 : Qle 0 (q_pow A (Datatypes.S k)))
    by (apply q_pow_nonneg; apply QleT'_to_Qle; exact HA).
  assert (HgeoQ : Qle ((1 + 1) * A) (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1))
    by (apply QleT'_to_Qle; exact Hgeom).
  pose proof (Qmult_le_compat_r _ _ _ HgeoQ HX0) as Hmid.
  setoid_rewrite (Qmult_comm (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                      (q_pow A (Datatypes.S k))) in Hmid.
  assert (Hstep : QleT' (A * q_pow A (Datatypes.S k))
                        ((1 / 2) * (q_pow A (Datatypes.S k)
                           * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))).
  { apply (rtb_qleT_trans _ ((1 / 2) * ((1 + 1) * A * q_pow A (Datatypes.S k)))).
    - apply qeq_leT'. field.
    - apply rtb_qleT_mult_l.
      + apply Qle_to_QleT'.
        apply (Qle_trans _ (((1 + 1) * A) * q_pow A (Datatypes.S k)));
          [apply qeq_le; ring | exact Hmid].
      + apply Qle_to_QleT'. unfold Qle. simpl. lia. }
  assert (HddD_nz : ~ (((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                          * q_fact (Datatypes.S k)) == 0)).
  { intro Hz.
    exact (q_neq_of_lt
             ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k))
             (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                (q_fact (Datatypes.S k))
                (QltT_to_Qlt _ _ (rtb_zpos_S (Datatypes.S k)))
                (q_fact_pos (Datatypes.S k))) Hz). }
  assert (HqD_nz : ~ (q_fact (Datatypes.S k) == 0)).
  { intro Hz. exact (q_neq_of_lt (q_fact (Datatypes.S k)) (q_fact_pos (Datatypes.S k)) Hz). }
  apply (rtb_qleT_trans _
    ((A * q_pow A (Datatypes.S k))
       / ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k)))).
  - apply rtb_qleT_refl.
  - apply (rtb_qleT_trans _
      (((1 / 2) * (q_pow A (Datatypes.S k)
             * (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)))
          / ((Z.of_nat (Datatypes.S (Datatypes.S k)) # 1) * q_fact (Datatypes.S k)))).
    + apply rtb_qleT_div_r.
      * exact Hstep.
      * apply Qlt_to_QltT.
        apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                                 (q_fact (Datatypes.S k))
                 (QltT_to_Qlt _ _ (rtb_zpos_S (Datatypes.S k)))
                 (q_fact_pos (Datatypes.S k))).
    + apply qeq_leT'. apply rtb_field_test.
      * apply QltT_to_Qlt. apply rtb_zpos_S.
      * apply q_fact_pos.
      * apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (Datatypes.S k)) # 1)
                                 (q_fact (Datatypes.S k))
                 (QltT_to_Qlt _ _ (rtb_zpos_S (Datatypes.S k)))
                 (q_fact_pos (Datatypes.S k))).
Qed.

(* 垫片：exp_tail_abs 消费形 == rtb_tsum 母定理形（如实计件：1 件） *)
Lemma rtb_exp_tsum_eq : forall (A : Q) (m d : nat),
  exp_tail_abs m (m + d)%nat A
    == rtb_tsum (fun k => rtb_exp_term A m k) 0%nat d.
Proof.
  intros A m d. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia.
    rewrite (exp_tail_abs_le_m m m A (Nat.le_refl m)). reflexivity.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d)) by lia.
    change (exp_tail_abs m (Datatypes.S (m + d)) A) with
      (exp_tail_abs m (m + d)%nat A
         + (if Nat.leb m (m + d)%nat
            then q_pow A (Datatypes.S (m + d)%nat) / q_fact (Datatypes.S (m + d)%nat)
            else 0)).
    assert (Hleb : (Nat.leb m (m + d)%nat) = true)
      by (apply (proj2 (Nat.leb_le m (m + d))); lia).
    rewrite Hleb.
    rewrite IH. rewrite rtb_tsum_S.
    replace (0 + d)%nat with d by lia. cbn beta. reflexivity.
Qed.

(* exp 位点实例（Q 层，真走 rtb_ratio_tail_Q） *)
Lemma rtb_exp_inst : forall (A : Q) (m n : nat),
  QleT' 0 A ->
  (forall t : nat, (m <= t)%nat -> QleT' ((1 + 1) * A) (Z.of_nat (t + 1)%nat # 1)) ->
  (m <= n)%nat ->
  QleT' (exp_tail_abs m n A)
        ((q_pow A (Datatypes.S m) / q_fact (Datatypes.S m))
           * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2))).
Proof.
  intros A m n HA Hgeom Hmn.
  replace n with ((m + (n - m))%nat) by lia.
  assert (Hrho0 : QleT' 0 (1 / 2)%Q) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (Hrho1 : QltT (1 / 2)%Q 1) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (Hcert : forall j : nat,
            QleT' (rtb_exp_term A m (Datatypes.S j)) ((1 / 2) * rtb_exp_term A m j)).
  { intro j. apply rtb_exp_ratio; assumption. }
  assert (Hq0 : rtb_exp_term A m 0%nat
                == q_pow A (Datatypes.S m) / q_fact (Datatypes.S m))
    by (unfold rtb_exp_term; replace (m + 0)%nat with m by lia; reflexivity).
  assert (HR : rtb_exp_term A m 0%nat
                 * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2))
               == q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)
                    * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2))).
  { rewrite Hq0. ring. }
  assert (Hshim2 : exp_tail_abs m n A
                     == rtb_tsum (rtb_exp_term A m) 0%nat (n - m)%nat).
  { pose proof (rtb_exp_tsum_eq A m (n - m)%nat) as Hs.
    replace ((m + (n - m))%nat) with n in Hs by lia. exact Hs. }
  replace (m + (n - m))%nat with n by lia.
  pose proof (rtb_ratio_tail_Q (rtb_exp_term A m) (1 / 2)%Q (n - m)%nat 0%nat
                Hrho0 Hrho1 Hcert) as Hmother.
  apply QleT'_to_Qle in Hmother.
  replace (m + 0)%nat with m in Hmother by lia.
  apply Qle_to_QleT'.
  - apply (rtb_qle_eq_l (exp_tail_abs m n A)
             (rtb_tsum (rtb_exp_term A m) 0%nat (n - m)%nat)
             (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)
                * ((1 - q_pow (1 / 2) (n - m)%nat) / (1 - 1 / 2)))).
    + exact Hshim2.
    + apply (rtb_qle_eq_r _ _ _ Hmother HR).
Qed.

(* real_const 间的 real_le（QleT' 提升供证书；Qle_lt_or_eq 判定分支） *)
Lemma rtb_rc_le : forall a b : Q, QleT' a b -> real_le (real_const a) (real_const b).
Proof.
  intros a b H.
  destruct (Qlt_le_dec a b) as [Hlt | Hle].
  - left.
    pose proof (rtb_qlt_0_minus a b Hlt) as Hba.
    assert (E : ((b - a) / 2)%Q == (1 / 2) * (b - a)) by (unfold Qdiv; ring).
    exists ((b - a) / 2)%Q. split.
    + apply Qlt_to_QltT. rewrite E. apply Qmult_lt_0_compat;
        [unfold Qlt; simpl; lia | exact Hba].
    + exists 0%nat. intros n Hn.
      cbn [projT1 real_const].
      apply Qlt_to_QltT. rewrite E.
      apply (Qlt_le_trans _ (1 * (b - a))).
      * assert (Hhalf : Qlt (1 / 2) 1) by (unfold Qlt; simpl; lia).
        apply (Qmult_lt_compat_r (1 / 2) 1 (b - a) Hba Hhalf).
      * apply qeq_le. apply Qmult_1_l.
  - right. apply rtb_rc_wd.
    apply (Qle_antisym a b).
    + apply QleT'_to_Qle. exact H.
    + exact Hle.
Qed.

(* const-const 乘积折叠回 const *)
Lemma rtb_rc_mult_eq : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a * b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_mult real_const]. ring.
Qed.

(* Real 层消费实例：Q 序列经 real_const 嵌入，真走 rtb_ratio_tail_real *)
Lemma rtb_exp_real_inst : forall (A : Q) (m N : nat),
  QleT' 0 A ->
  (forall t : nat, (m <= t)%nat -> QleT' ((1 + 1) * A) (Z.of_nat (t + 1)%nat # 1)) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt (rtb_rsum (fun k => real_const (rtb_exp_term A m k)) 0%nat N)
          (real_plus
             (real_mult (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                        (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2))))
             eps).
Proof.
  intros A m N HA Hgeom eps Heps.
  assert (Hrho0 : QleT' 0 (1 / 2)%Q) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (Hrho1 : QltT (1 / 2)%Q 1) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (Hcert : forall j : nat,
            real_le (real_const (rtb_exp_term A m (Datatypes.S j)))
                    (real_mult (real_const (1 / 2))
                               (real_const (rtb_exp_term A m j)))).
  { intro j.
    apply (real_le_trans (real_const (rtb_exp_term A m (Datatypes.S j)))
             (real_const ((1 / 2) * rtb_exp_term A m j))
             (real_mult (real_const (1 / 2)) (real_const (rtb_exp_term A m j)))).
    - apply rtb_rc_le.
      unfold rtb_exp_term.
      apply rtb_exp_ratio; assumption.
    - apply (RealSetoid.real_eq_le).
      apply (rtb_rc_mult_eq (1 / 2) (rtb_exp_term A m j)). }
  pose proof (rtb_ratio_tail_real (fun k => real_const (rtb_exp_term A m k))
                (1 / 2)%Q N 0%nat Hrho0 Hrho1 Hcert eps Heps) as H.
  assert (Hu0 : rtb_exp_term A m 0%nat
                == q_pow A (Datatypes.S m) / q_fact (Datatypes.S m))
    by (unfold rtb_exp_term; replace (m + 0)%nat with m by lia; reflexivity).
  apply (rtb_rlt_eq_r
           (rtb_rsum (fun k => real_const (rtb_exp_term A m k)) 0%nat N)
           (real_plus (real_mult (real_const (rtb_exp_term A m 0%nat))
                        (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps)
           (real_plus (real_mult (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                        (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps)
          (RealSetoid.real_eq_plus_compat
             (real_mult (real_const (rtb_exp_term A m 0%nat))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps
             (real_mult (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))) eps
             (RealSetoid.real_eq_mult_compat (real_const (rtb_exp_term A m 0%nat))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))
                (real_const (q_pow A (Datatypes.S m) / q_fact (Datatypes.S m)))
                (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))
                (rtb_rc_wd _ _ Hu0) (real_eq_refl (real_const ((1 - q_pow (1 / 2) N) / (1 - 1 / 2)))))
             (real_eq_refl eps))
          H).
Qed.

(* arctan 位点比值证书（无条件，闭式代数）：                          *)
(*   atan_mag (S j) x = |x|^{2j+3}/(2j+3) ≤ x²·atan_mag j x          *)
(*   （x² = |x|·|x| 承 atan_sq_abs；非线性目标禁 lia，走乘法单调）。   *)
Lemma rtb_atan_ratio : forall (x : Q) (j : nat),
  QleT' (atan_mag (Datatypes.S j) x) (Qabs x * Qabs x * atan_mag j x).
Proof.
  intros x j. unfold atan_mag.
  replace (2 * Datatypes.S j + 1)%nat with (2 * j + 3)%nat by lia.
  assert (Hdd : QltT 0 (Z.of_nat (2 * j + 3)%nat # 1)).
  { replace (2 * j + 3)%nat with (2 * Datatypes.S j + 1)%nat by lia.
    apply Qlt_to_QltT. apply atan_odd_pos. }
  assert (Hd1 : QltT 0 (Z.of_nat (2 * j + 1)%nat # 1))
    by (apply Qlt_to_QltT; apply atan_odd_pos).
  assert (Hprod : QltT 0 ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1)))
    by (apply Qlt_to_QltT;
        apply (Qmult_lt_0_compat (Z.of_nat (2 * j + 1)%nat # 1)
                                 (Z.of_nat (2 * j + 3)%nat # 1)
                                 (QltT_to_Qlt _ _ Hd1) (QltT_to_Qlt _ _ Hdd))).
  assert (HP0 : QleT' 0 (q_pow (Qabs x) (2 * j + 3)%nat))
    by (apply Qle_to_QleT'; apply q_pow_nonneg; apply Qabs_nonneg).
  assert (Hp : q_pow (Qabs x) (2 * j + 3)%nat
               == q_pow (Qabs x) (2 * j + 1)%nat * Qabs x * Qabs x).
  { replace (2 * j + 3)%nat with (Datatypes.S (Datatypes.S (2 * j + 1)))%nat by lia.
    simpl. ring. }
  assert (Hsub : QleT' (1 / (Z.of_nat (2 * j + 3)%nat # 1))
                       (1 / (Z.of_nat (2 * j + 1)%nat # 1))).
  { assert (Hle : QleT' (Z.of_nat (2 * j + 1)%nat # 1)
                        (Z.of_nat (2 * j + 3)%nat # 1))
      by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
    apply (rtb_qleT_trans _
             ((Z.of_nat (2 * j + 1)%nat # 1)
                / ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1)))).
    - apply qeq_leT'. unfold Qdiv. field.
      + split.
        * exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 3)%nat # 1) Hdd).
        * exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 1)%nat # 1) Hd1).
    - (* d1/(d1·dd) ≤ dd/(d1·dd) ≤ 1/d1：同分母除法保序 + 环账收口 *)
      apply (rtb_qleT_trans _
               ((Z.of_nat (2 * j + 3)%nat # 1)
                  / ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1)))).
      + apply (rtb_qleT_div_r
                   (Z.of_nat (2 * j + 1)%nat # 1)
                   (Z.of_nat (2 * j + 3)%nat # 1)
                   ((Z.of_nat (2 * j + 1)%nat # 1) * (Z.of_nat (2 * j + 3)%nat # 1))).
        * exact Hle.
        * exact Hprod.
      + apply qeq_leT'. unfold Qdiv. field.
        * split.
          -- exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 1)%nat # 1) Hd1).
          -- exact (rtb_neq_of_ltT (Z.of_nat (2 * j + 3)%nat # 1) Hdd). }
  apply (rtb_qleT_trans _
           (q_pow (Qabs x) (2 * j + 3)%nat * (1 / (Z.of_nat (2 * j + 1)%nat # 1)))).
  - apply (rtb_qleT_trans _
             (q_pow (Qabs x) (2 * j + 3)%nat * (1 / (Z.of_nat (2 * j + 3)%nat # 1)))).
    + apply qeq_leT'. unfold Qdiv. ring.
    + apply rtb_qleT_mult_l; [exact Hsub | exact HP0].
  - apply qeq_leT'. rewrite Hp. unfold Qdiv. ring.
Qed.

(* 指标平移证书：u (S j) ≤ x²·u j（u j := atan_mag (S (m+j)) x），      *)
(* 承 rtb_atan_ratio 于 j' := m + S j + atan_sq_abs 平方-绝对值切换。   *)
Lemma rtb_atan_cert : forall (x : Q) (m j : nat),
  QleT' (atan_mag (Datatypes.S (m + Datatypes.S j)%nat) x)
        ((x * x) * atan_mag (Datatypes.S (m + j)%nat) x).
Proof.
  intros x m j.
  pose proof (rtb_atan_ratio x (m + Datatypes.S j)%nat) as Hr.
  apply (rtb_qleT_trans _ ((Qabs x * Qabs x) * atan_mag (m + Datatypes.S j)%nat x)).
  - exact Hr.
  - apply qeq_leT'.
    replace (m + Datatypes.S j)%nat with (Datatypes.S (m + j)) by lia.
    rewrite (atan_sq_abs x). reflexivity.
Qed.

(* atan 位点实例（Q 层，真走 rtb_ratio_tail_Q）：|x|<1 时                *)
(*   Σ_{k<d} atan_mag (S (m+k)) x ≤ atan_mag (S m) x·(1-(x²)^d)/(1-x²)。 *)
Lemma rtb_atan_inst : forall (x : Q) (m d : nat),
  QltT (Qabs x) 1 ->
  QleT' (rtb_tsum (fun j => atan_mag (Datatypes.S (m + j)%nat) x) 0%nat d)
        (atan_mag (Datatypes.S m) x * ((1 - q_pow (x * x) d) / (1 - x * x))).
Proof.
  intros x m d Hx.
  assert (Hrho0 : QleT' 0 (x * x)).
  { apply (rtb_qleT_trans _ (Qabs x * Qabs x)).
    - apply Qle_to_QleT'. apply Qmult_le_0_compat; apply Qabs_nonneg.
    - apply qeq_leT'. apply Qeq_sym. apply atan_sq_abs. }
  assert (Hrho1 : QltT (x * x) 1).
  { apply Qlt_to_QltT.
    apply (Qle_lt_trans (x * x) (Qabs x * 1) (1 * 1)).
    - apply (Qle_trans (x * x) (Qabs x * Qabs x) (Qabs x * 1)).
      + apply qeq_le. apply atan_sq_abs.
      + rewrite (Qmult_comm (Qabs x) 1).
        apply Qmult_le_compat_r.
        * apply Qlt_le_weak. apply QltT_to_Qlt. exact Hx.
        * apply Qabs_nonneg.
    - apply (Qmult_lt_compat_r (Qabs x) 1 1).
      + unfold Qlt. simpl. lia.
      + apply QltT_to_Qlt. exact Hx. }
  assert (Hcert : forall j : nat,
            QleT' (atan_mag (Datatypes.S (m + Datatypes.S j)%nat) x)
                  ((x * x) * atan_mag (Datatypes.S (m + j)%nat) x))
    by (intro j; apply rtb_atan_cert).
  pose proof (rtb_ratio_tail_Q
                (fun j => atan_mag (Datatypes.S (m + j)%nat) x) (x * x) d 0%nat
                Hrho0 Hrho1 Hcert) as Hmother.
  cbv beta in Hmother.
  apply QleT'_to_Qle in Hmother.
  assert (Hu0 : atan_mag (Datatypes.S (m + 0)%nat) x
                  * ((1 - q_pow (x * x) d) / (1 - x * x))
                == atan_mag (Datatypes.S m) x
                  * ((1 - q_pow (x * x) d) / (1 - x * x)))
    by (replace (m + 0)%nat with m by lia; reflexivity).
  apply Qle_to_QleT'.
  exact (rtb_qle_eq_r
           (rtb_tsum (fun j => atan_mag (Datatypes.S (m + j)%nat) x) 0%nat d)
           (atan_mag (Datatypes.S (m + 0)%nat) x
              * ((1 - q_pow (x * x) d) / (1 - x * x)))
           (atan_mag (Datatypes.S m) x
              * ((1 - q_pow (x * x) d) / (1 - x * x)))
           Hmother Hu0).
Qed.

(* ============================================================ *)
(* 审计口：Print Assumptions                                   *)
(* ============================================================ *)

Print Assumptions rtb_ratio_tail_Q_mult.
Print Assumptions rtb_ratio_tail_Q.
Print Assumptions rtb_ratio_tail_real.
Print Assumptions rtb_exp_inst.
Print Assumptions rtb_exp_real_inst.
Print Assumptions rtb_atan_inst.
