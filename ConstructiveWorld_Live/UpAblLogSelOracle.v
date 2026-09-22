(* ============================================================ *)
(* UpAblLogSelOracle.v —— 席AID2：局限(1b)·神谕前件 Real 层对数选择器          *)
(*                                                              *)
(* 【零承认件】本件零承认、零假设负载、零经典逻辑：全文无任何全局无据项。       *)
(* 四关卡全绿＝LOGSEL 定谳席 20260921 净室重编实测锚定（非沿旧申报）：          *)
(*   G1 源面禁词 0＋17 路审计口 Print Assumptions 全 Closed；                  *)
(*   G2 全量编译 EXIT=0＋vo 头魔数 436f712100015ff4＋vo 新于 v；               *)
(*   G3 独立目录提取 32 件（16.ml+16.mli）Obj.magic 合计 0；                   *)
(*   G4 coqchk 全闭包 rc=0＋CONTEXT SUMMARY「Axioms: <none>」。                *)
(* 旧账销讫：T3「L176 编译失败」系 Qcompare_eq_iff 旧源时代过账，现源三支       *)
(*   已 Z.compare_eq_iff / Z.compare_lt_iff / Z.compare_gt_iff 修复，          *)
(*   净室重编零伤——「修复已落而账未销」定谳成立，账随本定谳销讫；              *)
(*   证据图谱：attn\_tlogsel_定谳报告-20260921.md。                            *)
(*                                                              *)
(* 目的：论文 7 limitation (1) 的正解路线——带「逐站可判定探测」显式前件的       *)
(*   Real 层对数级选择器。N2（UpAblLogWall.v）已定理化：不带可判定测试前件的    *)
(*   Real 层精确最小站选择器 ⟹ LPO 族实例（序判定缺位=墙）。本件给「器」侧：    *)
(*   神谕（逐站 bool 探测及其 Real 语义两账）在场时，对数级选择器构造性可达，    *)
(*   与 N2 墙定理构成「墙+器」配对叙事（双测清算）。                          *)
(*                                                              *)
(* 诚实前件先例谱系：§6.3 le 形 Archimedean 诚实前件（UpReqUMixSelect.v        *)
(*   ums_k_select 的 le 形 Arch 前件直给）——接口缺口以显式前件承载，本件把     *)
(*   「线性无器」升格为「对数有器」：每站一个可判定 bool 探测，真支供隙         *)
(*   （real_lt κ^k·TV₀ < budget），假支否证（real_le budget ≤ κ^k·TV₀），       *)
(*   两账形镜像 mixa_sel_accounts / mixb_sel_scale 的 test 语义。             *)
(*                                                              *)
(* 承重消费件（零改动）：UpReqMixLogB 泛型搜索核 mixb_sel/mixb_gallop/          *)
(*   mixb_bsearch（nat/bool 泛型）+ mixb_sel_scale（fuel=2+⌊log₂K⌋ 双相配给     *)
(*   量级定理：返回恰为最小通过站且比较次数 ≤ 2·log₂K+5）+ mixb_enum 账；      *)
(*   UpReqIterGeomRate igr_k_enum 三账（sound/none/min）最小通过站枚举；       *)
(*   KLWallClosed klc_closed_powb_mono + RateTheoryAblation rta_strict_branch_ *)
(*   real / rta_rpow_powb_eq（Bishop 形实形消费，见下申报）。                  *)
(*                                                              *)
(* 三件交付：                                                                *)
(*   件① loso_test_oracle（探测前件定义）：∀k, sigT (b:bool) × loso_sem b k，   *)
(*      loso_sem b k = And (Id b true → real_lt κ^k·TV₀ budget)               *)
(*                       (Id b false → real_le budget κ^k·TV₀)。              *)
(*      bool 等式取基座 Id（Set 层恒等族，QltT 同款）——语句面全 Set、零 Prop    *)
(*      泄露；Prop 面桥（stdlib eq 形）以 Qed 伴生件 loso_oracle_true_lt /      *)
(*      loso_oracle_false_le 承载。假支方向定谳：mixa_sel_accounts 两账中      *)
(*      test j = false ⟺ b₀ ≤ κ₀^j·v（mixa_min_real_below 下向界），故 Real    *)
(*      面假支取 real_le budget (κ^j·TV₀)——与真支互斥，构成「真支供隙+假支      *)
(*      否证」的诚实二分。神谕在场实证钉：loso_oracle_const（const 层 Qcompare *)
(*      可判定分裂实现本前件，非空泛假设——N2 lgw_oracle_pin 的正向对偶）。      *)
(*   件② loso_k_select_log（Defined sigT 可提取）+ loso_k_select_log_le        *)
(*      （le 形，§6.3 先例同构）：fun k => projT1 (Htest k) 直喂 mixb_sel       *)
(*      （fuel 双相 S(S(log2 K))），输出站 r 满足 real_lt κ^r·TV₀ < budget。    *)
(*   件③ loso_sel_accounts（Prop 三账：通过+以下全败+比较数对数级）+           *)
(*      loso_sel_pass / loso_sel_below_fail（Real 侧语义两账，经件①前件桥接）。 *)
(*                                                              *)
(* 单调性腿（幂列递减）双轨申报：                                             *)
(*   (a) 实形消费轨：loso_powb_mono_b（消费 klc_closed_powb_mono：底 (1−κ)      *)
(*      Bishop 幂单调，经 rta_rpow_powb_eq 运载至 tv_rpow——rta_omd_powb_mono_b *)
(*      同法）与 loso_strict_shrink（消费 rta_strict_branch_real：0≤κ<1 严格支  *)
(*      正性证书 × Bishop 收缩打包）。                                        *)
(*   (b) 本件承重轨：loso_rpow_dec_le（底 κ、Or 编码 real_le 形指数单调，直接  *)
(*      归纳自证）——树内 UpRealLeB 仅有 real_le→real_le_b 单向桥，Bishop→Or    *)
(*      反向桥缺席，(a) 轨无法直接承载本件矛盾账，故 (b) 直接归纳；两轨并存     *)
(*      如实申报，非降档（(a) 全量消费实形、(b) 全量真证）。                   *)
(*                                                              *)
(* 窗口配给申报（量力择一）：显式 K 前件形——Hhit : exists k, k ≤ K ∧ 探测 k 真   *)
(*   窗命中假设（mixb_qsel_account_ex Hhit 形同构），非 real_arch 发散兜底形；  *)
(*   因本件 κ/TV₀/budget 为抽象 Real+神谕语义面，mixb 主件的 Q-Bernoulli 窗口  *)
(*   账需 const 层证书链（mixb_k_select_log 已承），本件不重复该链。            *)
(*                                                              *)
(* 红线自审：①纯构造性（前件为显式函数参；零全局无据项；Qed 件内 Not/False    *)
(*   仅构造性消费）；②Set 层零 Prop 泄露（选择器 sigT Defined 全 Set 载荷；    *)
(*   bool 账等式用基座 Id；两账/三账 Prop 面 Qed 不入提取签名）；③非平凡件     *)
(*   全量真证，缺口逐条显式申报；④Set 组件 Separate Extraction 魔术字零。      *)
(* 依赖：CW_ConstructiveWorld_219、UpTVDoeblin（tv_rpow）、UpReqIterGeomRate    *)
(*   （igr_k_enum 三账）、UpReqMixLogB（mixb_sel 泛型核+mixb_sel_scale 量级）、 *)
(*   KLWallClosed（klc_closed_powb_mono）、RateTheoryAblation（rta 两件）、     *)
(*   Stdlib QArith/Lia/Extraction。                                          *)
(* 编译配方（9.1 直调轨，unset COQLIB ROCQLIB，全路径全量）：                   *)
(*   C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe -q -Q . "" UpAblLogSelOracle.v *)
(* AID2（20260920）：新建。                                                  *)
(* LOGSEL（20260921）：T3 L176 旧伤定谳＝修复已落账未销；头注如实化＋四关      *)
(*   重锚全绿（净室全量 coqc＋G3 独立目录提取＋G4 coqchk，零源语义改动）。     *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqMixLogB.
Require Import KLWallClosed.
Require Import RateTheoryAblation.
Require Import UpRealLeB.
Require Import G07_KLWall.

(* ============================================================ *)
(* Part 0：换形小件（real_le_b 的两侧 eq 运载；real_le 侧消费                   *)
(*   RealSetoid.real_le_compat 既有件）                                       *)
(* ============================================================ *)

Lemma loso_le_b_compat : forall x y x' y' : Real,
  real_eq x x' -> real_eq y y' -> real_le_b x y -> real_le_b x' y'.
Proof.
  intros x y x' y' Hx Hy Hb. unfold real_le_b in *. intros eps Heps.
  apply (RealSetoid.real_lt_compat x x' (real_plus y eps) (real_plus y' eps)).
  - exact Hx.
  - exact (RealSetoid.real_eq_plus_compat y eps y' eps Hy (real_eq_refl eps)).
  - exact (Hb eps Heps).
Qed.

(* ============================================================ *)
(* Part 1：件① 探测前件（loso_test_oracle）+ 探针 + 语义桥 + 神谕在场钉        *)
(* ============================================================ *)

(* 每站语义两账：真支供隙（real_lt），假支否证（real_le budget ≤ κ^k·TV₀）。 *)
(* bool 等式取基座 Id（Set 层恒等族）——语句面全 Set。                       *)
Definition loso_sem (kappa TV0 budget : Real) (b : bool) (k : nat) : Set :=
  And (Id b true -> real_lt (real_mult (tv_rpow kappa k) TV0) budget)
      (Id b false -> real_le budget (real_mult (tv_rpow kappa k) TV0)).

(* 件①：逐站可判定探测的诚实前件（神谕形）。 *)
Definition loso_test_oracle (kappa TV0 budget : Real) : Set :=
  forall k : nat, sigT (fun b : bool => loso_sem kappa TV0 budget b k).

(* 探针：神谕第 k 站返回的 bool——直喂泛型搜索核的 test 函数。 *)
Definition loso_probe (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget) : nat -> bool :=
  fun k => projT1 (Htest k).

(* Prop 面桥（Qed 伴生，不入提取签名）：探测真 ⟹ 供隙。 *)
Lemma loso_oracle_true_lt : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget) (k : nat),
  loso_probe kappa TV0 budget Htest k = true ->
  real_lt (real_mult (tv_rpow kappa k) TV0) budget.
Proof.
  intros kappa TV0 budget Htest k H. unfold loso_probe in H.
  destruct (Htest k) as [b Hcert] eqn:EH.
  cbn [projT1] in H. subst b.
  destruct Hcert as [Hc1 Hc2]. exact (Hc1 (@id_refl bool true)).
Qed.

(* Prop 面桥（Qed 伴生）：探测假 ⟹ 否证。 *)
Lemma loso_oracle_false_le : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget) (k : nat),
  loso_probe kappa TV0 budget Htest k = false ->
  real_le budget (real_mult (tv_rpow kappa k) TV0).
Proof.
  intros kappa TV0 budget Htest k H. unfold loso_probe in H.
  destruct (Htest k) as [b Hcert] eqn:EH.
  cbn [projT1] in H. subst b.
  destruct Hcert as [Hc1 Hc2]. exact (Hc2 (@id_refl bool false)).
Qed.

(* —— 神谕在场实证钉（N2 lgw_oracle_pin 的正向对偶）：const 层本前件可实现 —— *)
(*    （Qcompare 可判定分裂供 bool，mixb const 桥供 Real 语义两账）——本前件    *)
(*    非空泛假设，序判定缺位仅在离开 const 层处成墙。                          *)
Lemma loso_oracle_const : forall (a v b0 : Q),
  loso_test_oracle (real_const a) (real_const v) (real_const b0).
Proof.
  intros a v b0 k.
  pose (X := (Qmult (igr_qpow a k) v)%Q).
  assert (Heq : real_eq (real_mult (tv_rpow (real_const a) k) (real_const v))
                  (real_const X)).
  { apply (real_eq_trans
             (real_mult (tv_rpow (real_const a) k) (real_const v))
             (real_mult (real_const (igr_qpow a k)) (real_const v))
             (real_const X)).
    - exact (RealSetoid.real_eq_mult_compat (tv_rpow (real_const a) k)
               (real_const v) (real_const (igr_qpow a k)) (real_const v)
               (mixb_const_rpow_eq a k) (real_eq_refl (real_const v))).
    - exact (real_eq_sym (real_const (Qmult (igr_qpow a k) v))
               (real_mult (real_const (igr_qpow a k)) (real_const v))
               (mixb_const_mult (igr_qpow a k) v)). }
  assert (Heqs : real_eq (real_const X)
                   (real_mult (tv_rpow (real_const a) k) (real_const v))).
  { exact (real_eq_sym (real_mult (tv_rpow (real_const a) k) (real_const v))
             (real_const X) Heq). }
  destruct (Qcompare b0 X) eqn:E.
  - (* Eq：假支（否证） *)
    unfold Qcompare in E.
    pose proof (proj1 (Z.compare_eq_iff (Qnum b0 * QDen X)%Z
                         (Qnum X * QDen b0)%Z) E) as Hze.
    exists false. split.
    + intro Hid. inversion Hid.
    + intro Hdead.
      exact (RealSetoid.real_le_compat (real_const b0) (real_const b0)
               (real_const X)
               (real_mult (tv_rpow (real_const a) k) (real_const v))
               (real_eq_refl (real_const b0)) Heqs
               (mixb_qle_const_le b0 X (qeq_le b0 X Hze))).
  - (* Lt：假支（否证） *)
    unfold Qcompare in E.
    pose proof (proj1 (Z.compare_lt_iff (Qnum b0 * QDen X)%Z
                         (Qnum X * QDen b0)%Z) E) as Hzl.
    exists false. split.
    + intro Hid. inversion Hid.
    + intro Hdead.
      exact (RealSetoid.real_le_compat (real_const b0) (real_const b0)
               (real_const X)
               (real_mult (tv_rpow (real_const a) k) (real_const v))
               (real_eq_refl (real_const b0)) Heqs
               (mixb_qle_const_le b0 X (Qlt_le_weak b0 X Hzl))).
  - (* Gt：真支（供隙）——Z.compare_gt_iff 直接回取 Qlt X b0 *)
    unfold Qcompare in E.
    pose proof (proj1 (Z.compare_gt_iff (Qnum b0 * QDen X)%Z
                         (Qnum X * QDen b0)%Z) E) as Hzg.
    exists true. split.
    + intro Hdead.
      exact (RealSetoid.real_lt_compat (real_const X)
               (real_mult (tv_rpow (real_const a) k) (real_const v))
               (real_const b0) (real_const b0)
               (real_eq_sym (real_mult (tv_rpow (real_const a) k)
                                 (real_const v)) (real_const X) Heq)
               (real_eq_refl (real_const b0))
               (mixb_Qlt_const_lt X b0 Hzg)).
    + intro Hid. inversion Hid.
Qed.

(* ============================================================ *)
(* Part 2：单调性腿——幂列递减                                                  *)
(*   (a) 实形消费轨（Bishop 形，klc_closed_powb_mono / rta_strict_branch_real）*)
(*   (b) 本件承重轨（Or 编码 real_le 形，直接归纳）                            *)
(* ============================================================ *)

(* —— (a) 轨一：klc_closed_powb_mono 实形（底 1−κ，0≤κ≤1 全量）经             *)
(*    rta_rpow_powb_eq 运载至 tv_rpow（rta_omd_powb_mono_b 同法） —— *)
(* —— (a) 轨运载器：powb_pow ⟶ tv_rpow 的 Bishop 单调搬运（rta §5 同法） —— *)
Lemma loso_le_b_rpow_transport : forall (B : Real) (m n : nat),
  real_le_b (powb_pow B m) (powb_pow B n) ->
  real_le_b (tv_rpow B m) (tv_rpow B n).
Proof.
  intros B m n Hbb.
  apply (loso_le_b_compat (powb_pow B m) (powb_pow B n)).
  - exact (real_eq_sym (tv_rpow B m) (powb_pow B m) (rta_rpow_powb_eq B m)).
  - exact (real_eq_sym (tv_rpow B n) (powb_pow B n) (rta_rpow_powb_eq B n)).
  - exact Hbb.
Qed.

Lemma loso_powb_mono_b : forall (kappa : Real) (j j' : nat),
  real_le real_zero kappa -> real_le kappa real_one -> (j <= j')%nat ->
  real_le_b (tv_rpow (real_plus real_one (real_opp kappa)) j')
            (tv_rpow (real_plus real_one (real_opp kappa)) j).
Proof.
  intros kappa j j' H0 H1 Hjj.
  apply (loso_le_b_rpow_transport (real_plus real_one (real_opp kappa)) j' j).
  exact (klc_closed_powb_mono kappa j j' H0 H1 (NatLe_lift j j' Hjj)).
Qed.

(* —— (a) 轨二：rta_strict_branch_real 实形（0≤κ<1 严格支打包）运载 —— *)
Lemma loso_strict_shrink : forall (kappa : Real) (j j' : nat),
  real_le real_zero kappa -> real_lt kappa real_one -> (j <= j')%nat ->
  prod (real_lt real_zero (real_plus real_one (real_opp kappa)))
       (real_le_b (tv_rpow (real_plus real_one (real_opp kappa)) j')
                  (tv_rpow (real_plus real_one (real_opp kappa)) j)).
Proof.
  intros kappa j j' H0 Hlt Hjj.
  pose proof (rta_strict_branch_real kappa j j' H0 Hlt (NatLe_lift j j' Hjj))
    as [Hpos Hbb].
  split.
  - exact Hpos.
  - apply (loso_le_b_rpow_transport (real_plus real_one (real_opp kappa)) j' j).
    exact Hbb.
Qed.

(* —— (b) 轨承重件：Or 编码 real_le 形幂非负不变量 —— *)
Lemma loso_rpow_nonneg : forall (kappa : Real) (k : nat),
  real_le real_zero kappa -> real_le real_zero (tv_rpow kappa k).
Proof.
  intros kappa k H0. induction k as [| m IH].
  - exact (inl real_lt_zero_one).
  - cbn [tv_rpow].
    apply (real_le_trans real_zero (real_mult real_zero (tv_rpow kappa m))
             (real_mult kappa (tv_rpow kappa m))).
    + apply (RealSetoid.real_eq_le real_zero
               (real_mult real_zero (tv_rpow kappa m))).
      exact (real_eq_sym (real_mult real_zero (tv_rpow kappa m)) real_zero
               (real_eq_trans (real_mult real_zero (tv_rpow kappa m))
                  (real_mult (tv_rpow kappa m) real_zero) real_zero
                  (real_mult_comm real_zero (tv_rpow kappa m))
                  (real_mult_zero (tv_rpow kappa m)))).
    + exact (real_le_mult_compat_weak real_zero kappa (tv_rpow kappa m) IH H0).
Qed.

(* —— (b) 轨承重件：单步递减 κ^{S m} ≤ κ^m（0≤κ≤1） —— *)
Lemma loso_rpow_step_le : forall (kappa : Real) (m : nat),
  real_le real_zero kappa -> real_le kappa real_one ->
  real_le (tv_rpow kappa (Datatypes.S m)) (tv_rpow kappa m).
Proof.
  intros kappa m H0 H1.
  pose proof (loso_rpow_nonneg kappa m H0) as Hnn.
  cbn [tv_rpow].
  apply (real_le_trans (real_mult kappa (tv_rpow kappa m))
           (real_mult real_one (tv_rpow kappa m)) (tv_rpow kappa m)).
  - exact (real_le_mult_compat_weak kappa real_one (tv_rpow kappa m) Hnn H1).
  - exact (RealSetoid.real_eq_le (real_mult real_one (tv_rpow kappa m))
             (tv_rpow kappa m)
             (real_eq_trans (real_mult real_one (tv_rpow kappa m))
                (real_mult (tv_rpow kappa m) real_one) (tv_rpow kappa m)
                (real_mult_comm real_one (tv_rpow kappa m))
                (real_mult_one (tv_rpow kappa m)))).
Qed.

(* —— (b) 轨主件：全量指数单调 κ^{j'} ≤ κ^j（0≤κ≤1，Or 编码 real_le 形）。
   序界取 Set 层 NatLe（Prop 面 le 的归纳不可消去入 Set——本件撞墙点，
   klc_powb_mono_weak 同款 nat 归纳 + NatLe_lift/drop 桥绕行）—— *)
Lemma loso_rpow_dec_le : forall (kappa : Real) (j j' : nat),
  real_le real_zero kappa -> real_le kappa real_one -> NatLe j j' ->
  real_le (tv_rpow kappa j') (tv_rpow kappa j).
Proof.
  intros kappa j j' H0 H1. revert j. induction j' as [| m IH]; intros j Hjj.
  - (* j' = 0：NatLe j 0 ⟹ j = 0（leb (S n) 0 ≡ false 爆破） *)
    destruct j as [| n].
    + exact (real_le_refl (tv_rpow kappa 0%nat)).
    + exfalso.
      unfold NatLe in Hjj.
      pose proof (@id_trans bool (Nat.leb (Datatypes.S n) 0%nat) false true
                    (@id_refl bool false) Hjj) as Hbad.
      inversion Hbad.
  - (* j' = S m：leb j m 分裂（klc_powb_mono_weak 同法） *)
    destruct (Nat.leb j m) eqn:E2.
    + apply (real_le_trans (tv_rpow kappa (Datatypes.S m))
               (tv_rpow kappa m) (tv_rpow kappa j)).
      * exact (loso_rpow_step_le kappa m H0 H1).
      * apply IH. apply (NatLe_lift j m).
        exact (proj1 (Nat.leb_le j m) E2).
    + pose proof (proj1 (Nat.leb_gt j m) E2) as Hgt.
      pose proof (NatLe_drop j (Datatypes.S m) Hjj) as Hjle.
      assert (Heq : j = Datatypes.S m) by lia.
      rewrite Heq. exact (real_le_refl (tv_rpow kappa (Datatypes.S m))).
Qed.

(* ============================================================ *)
(* Part 3：探针单调账（真支供隙+假支否证+幂列递减 ⟹ 过站集上闭）               *)
(* ============================================================ *)

Lemma loso_probe_mono : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget),
  real_le real_zero kappa -> real_le kappa real_one ->
  real_le real_zero TV0 ->
  mixb_mono (loso_probe kappa TV0 budget Htest).
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha j j' Hjj Hj.
  pose proof (loso_rpow_dec_le kappa j j' Hk0 Hk1 (NatLe_lift j j' Hjj))
    as Hdec.
  (* 站 j 语义：探测真 ⟹ κ^j·TV₀ < budget *)
  assert (Hltj : real_lt (real_mult (tv_rpow kappa j) TV0) budget).
  { exact (loso_oracle_true_lt kappa TV0 budget Htest j Hj). }
  (* 站 j' 语义取支 *)
  destruct (Htest j') as [b Hcert] eqn:Ej'.
  unfold loso_probe. rewrite Ej'. cbn [projT1].
  destruct b as [].
  - reflexivity.
  - exfalso.
    (* 假支语义证书：budget ≤ κ^{j'}·TV₀ *)
    destruct Hcert as [Hc1 Hc2].
    pose proof (Hc2 (@id_refl bool false)) as Hlej'.
    (* 幂列递减 × 乘法弱保序 ⟹ budget ≤ κ^j·TV₀，与供隙支相撞 *)
    assert (Hmul : real_le (real_mult (tv_rpow kappa j') TV0)
                     (real_mult (tv_rpow kappa j) TV0))
      by exact (real_le_mult_compat_weak (tv_rpow kappa j')
                  (tv_rpow kappa j) TV0 Ha Hdec).
    assert (Hbl : real_le budget (real_mult (tv_rpow kappa j) TV0))
      by exact (real_le_trans budget (real_mult (tv_rpow kappa j') TV0)
                  (real_mult (tv_rpow kappa j) TV0) Hlej' Hmul).
    unfold real_le in Hbl. destruct Hbl as [Hltb | Heqb].
    + exact (match (real_lt_irrefl (real_mult (tv_rpow kappa j) TV0)
                     (real_lt_trans (real_mult (tv_rpow kappa j) TV0) budget
                        (real_mult (tv_rpow kappa j) TV0) Hltj Hltb)) with end).
    + exact (match (real_lt_irrefl (real_mult (tv_rpow kappa j) TV0)
                     (RealSetoid.real_lt_compat
                        (real_mult (tv_rpow kappa j) TV0)
                        (real_mult (tv_rpow kappa j) TV0)
                        budget (real_mult (tv_rpow kappa j) TV0)
                        (real_eq_refl (real_mult (tv_rpow kappa j) TV0))
                        Heqb Hltj)) with end).
Qed.

(* ============================================================ *)
(* Part 4：件③ 账面——Prop 三账 + Real 侧语义两账                              *)
(* ============================================================ *)

(* 三账（Prop 面，mixb_qsel_account_ex 神谕化镜像）：返回站通过、以下全败、      *)
(* 比较数对数级（fuel 双相 2+⌊log₂K⌋ 配给，量级 2·log₂K+5）。 *)
Theorem loso_sel_accounts : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K r c : nat),
  (2 <= K)%nat ->
  loso_probe kappa TV0 budget Htest 0%nat = false ->
  (exists k : nat, (k <= K)%nat /\
                   loso_probe kappa TV0 budget Htest k = true) ->
  mixb_sel (loso_probe kappa TV0 budget Htest)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  loso_probe kappa TV0 budget Htest r = true /\
  (forall j : nat, (j < r)%nat ->
                   loso_probe kappa TV0 budget Htest j = false) /\
  (c <= 2 * (Nat.log2 K) + 5)%nat.
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha K r c HK2 Hmiss0 Hhit Hsel.
  pose proof (loso_probe_mono kappa TV0 budget Htest Hk0 Hk1 Ha) as Hmono.
  destruct Hhit as [k0 [Hk0K Hk0pass]].
  destruct (igr_k_enum (loso_probe kappa TV0 budget Htest) K) as [kmin|]
    eqn:Eenum.
  - (* 窗内最小通过站命中：mixb_sel_scale 量级账合龙 *)
    pose proof (igr_k_enum_sound _ _ _ Eenum) as Hpassmin.
    pose proof (igr_k_enum_min _ _ _ Eenum) as Hminmin.
    pose proof (mixb_enum_le _ _ _ Eenum) as HminK.
    assert (Hkmin1 : (1 <= kmin)%nat).
    { destruct kmin as [| m].
      - rewrite Hmiss0 in Hpassmin. discriminate Hpassmin.
      - lia. }
    destruct (mixb_sel_scale (loso_probe kappa TV0 budget Htest) K kmin r c
                Hmono Hmiss0 Hpassmin Hminmin Hkmin1 HminK HK2 Hsel)
      as [Hr Hc].
    rewrite Hr. split.
    + exact Hpassmin.
    + split.
      * exact Hminmin.
      * exact Hc.
  - (* None 支与窗命中假设相撞 *)
    exfalso.
    pose proof (igr_k_enum_none (loso_probe kappa TV0 budget Htest) K Eenum
                  k0 Hk0K) as HF.
    rewrite Hk0pass in HF. discriminate HF.
Qed.

(* Real 侧通过账（真支供隙）：输出站 r 处 κ^r·TV₀ < budget。 *)
Theorem loso_sel_pass : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K r c : nat),
  (2 <= K)%nat ->
  loso_probe kappa TV0 budget Htest 0%nat = false ->
  (exists k : nat, (k <= K)%nat /\
                   loso_probe kappa TV0 budget Htest k = true) ->
  mixb_sel (loso_probe kappa TV0 budget Htest)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  real_lt (real_mult (tv_rpow kappa r) TV0) budget.
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha K r c HK2 Hmiss0 Hhit Hsel.
  destruct (loso_sel_accounts kappa TV0 budget Htest Hk0 Hk1 Ha K r c
               HK2 Hmiss0 Hhit Hsel) as [Hpass _].
  exact (loso_oracle_true_lt kappa TV0 budget Htest r Hpass).
Qed.

(* Real 侧全败账（假支否证）：j < r ⟹ budget ≤ κ^j·TV₀（真最小站下向界，       *)
(* mixa_min_real_below 形的神谕化镜像）。                                      *)
Theorem loso_sel_below_fail : forall (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K r c : nat),
  (2 <= K)%nat ->
  loso_probe kappa TV0 budget Htest 0%nat = false ->
  (exists k : nat, (k <= K)%nat /\
                   loso_probe kappa TV0 budget Htest k = true) ->
  mixb_sel (loso_probe kappa TV0 budget Htest)
    (Datatypes.S (Datatypes.S (Nat.log2 K)))
    (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  forall j : nat, (j < r)%nat ->
    real_le budget (real_mult (tv_rpow kappa j) TV0).
Proof.
  intros kappa TV0 budget Htest Hk0 Hk1 Ha K r c HK2 Hmiss0 Hhit Hsel
    j Hj.
  destruct (loso_sel_accounts kappa TV0 budget Htest Hk0 Hk1 Ha K r c
               HK2 Hmiss0 Hhit Hsel) as [Hpass Hrest].
  destruct Hrest as [Hmin _].
  exact (loso_oracle_false_le kappa TV0 budget Htest j (Hmin j Hj)).
Qed.

(* ============================================================ *)
(* Part 5：件② 对数选择器（Defined sigT 可提取）+ le 形（§6.3 先例同构）        *)
(* ============================================================ *)

Definition loso_k_select_log (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K : nat) (HK2 : (2 <= K)%nat)
  (Hmiss0 : loso_probe kappa TV0 budget Htest 0%nat = false)
  (Hhit : exists k : nat, (k <= K)%nat /\
                          loso_probe kappa TV0 budget Htest k = true)
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct (mixb_sel (loso_probe kappa TV0 budget Htest)
              (Datatypes.S (Datatypes.S (Nat.log2 K)))
              (Datatypes.S (Datatypes.S (Nat.log2 K)))) as [r c] eqn:Hsel.
  exists r.
  exact (loso_sel_pass kappa TV0 budget Htest Hk0 Hk1 Ha K r c
           HK2 Hmiss0 Hhit Hsel).
Defined.

(* le 形（§6.3 le 形诚实前件先例同构：real_lt_le_iff_req 左支直给） *)
Definition loso_k_select_log_le (kappa TV0 budget : Real)
  (Htest : loso_test_oracle kappa TV0 budget)
  (Hk0 : real_le real_zero kappa) (Hk1 : real_le kappa real_one)
  (Ha : real_le real_zero TV0)
  (K : nat) (HK2 : (2 <= K)%nat)
  (Hmiss0 : loso_probe kappa TV0 budget Htest 0%nat = false)
  (Hhit : exists k : nat, (k <= K)%nat /\
                          loso_probe kappa TV0 budget Htest k = true)
  : sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  destruct (loso_k_select_log kappa TV0 budget Htest Hk0 Hk1 Ha K HK2
              Hmiss0 Hhit) as [k Hk].
  exists k.
  exact (RealSetoid.real_lt_le_iff_req (real_mult (tv_rpow kappa k) TV0)
           budget (inl Hk)).
Defined.

(* ============================================================ *)
(* Part 6：审计口（G2/G3 关卡面）                                              *)
(* ============================================================ *)

Print Assumptions loso_sem.
Print Assumptions loso_test_oracle.
Print Assumptions loso_probe.
Print Assumptions loso_oracle_true_lt.
Print Assumptions loso_oracle_false_le.
Print Assumptions loso_oracle_const.
Print Assumptions loso_powb_mono_b.
Print Assumptions loso_strict_shrink.
Print Assumptions loso_rpow_nonneg.
Print Assumptions loso_rpow_step_le.
Print Assumptions loso_rpow_dec_le.
Print Assumptions loso_probe_mono.
Print Assumptions loso_sel_accounts.
Print Assumptions loso_sel_pass.
Print Assumptions loso_sel_below_fail.
Print Assumptions loso_k_select_log.
Print Assumptions loso_k_select_log_le.

Separate Extraction loso_sem loso_test_oracle loso_probe loso_k_select_log loso_k_select_log_le.
