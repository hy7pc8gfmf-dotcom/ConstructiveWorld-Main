(* ===================================================================== *)
(*  abl_ln2_theta_rehook.v —— ln2 无理性链·θ=4/5 上肢回接+常数更新装配件    *)
(*  使命: 把 abl_ln2_theta_upper 件的 θ=4/5 上肢（lnt2_hquad 二次界   *)
(*        ＋lnt2_theta_budget θ 预算＋lnt2_wgap_geo_quarter 组合终形        *)
(*        C: 2^{n+3}→2^{n+2}）回接进 lnw/lna 链，三肢一线:                  *)
(*        ①lnw 链常数更新——lnw_wgap_geo 的 C:=2^{n+3} 由 2^{n+2} 改进替代   *)
(*          （同窗 2n≤M+1、同率 ρ=3/4、常数减半）: 替代名替代形 lnr2_wgap_  *)
(*          geo（exact lnt2_wgap_geo_quarter）＋锐权尾隙/换序误差肢的半常数 *)
(*          版（lnr2_wtail_geo/lnr2_wgap_limb，使用 DA 通用相消机           *)
(*          lnf_range_gap_cancel/lnf_tail_transport/lnf_sum_scale_r）＋     *)
(*          旧形保留为推论（lnr2_wgap_geo_legacy/lnr2_wtail_geo_legacy:     *)
(*          2^{n+2}≤2^{n+3} 的显式单调闭合，旧使用面全数可用）；            *)
(*        ②θ 组合肢接入 lna_supply_rem' 装配——lna_theta_mod（=4/5）命名槽   *)
(*          上的 θ 预算（lnr2_theta_budget_rem: 4ⁿ(7/40)ⁿ≤θⁿ）＋real 常值   *)
(*          比较微桥（lnr2_const_eq/lt/le）＋上界肢使用桥                   *)
(*          （lnr2_rem_upper_of_budget: 预算面供给者⟹ln2b_line_upper）＋    *)
(*          两肢装配 hook（lnr2_supply_rem_theta_hook: 上肢由 θ 预算面接入， *)
(*          下界肢如实悬置——S6 恒等式腿候选件不虚报）＋锐权衰减消失引擎     *)
(*          （lnr2_wgapbound_vanish/lnr2_wvanish: 2^{n+2}(3/4)^{SM−2n}<eps  *)
(*          的显式配方 N:=2n+4·2^{n+2}·den(eps)，装配件诚实边界所列          *)
(*          「锐权衰减」腿的半常数承载）。                                  *)
(*  依赖: Stdlib QArith(QArith+Qabs)/Arith/ZArith/Lia；S01_BaseRing          *)
(*        S02_CauchyComplete S03_QExp Ln2Bridge PolyIntegral                *)
(*        PadeErrorIntegral BeukersLists BeukersVariant PintMono            *)
(*        PsQReindex RealIdentity；前置池拷贝链序                           *)
(*        abl_ln2_tail_bound → abl_ln2_numer_int → abl_ln2_sharp_weight →  *)
(*        abl_ln2_ireal → abl_ln2_reorder → abl_ln2_assembly →             *)
(*        abl_ln2_theta_upper（各件头注 Require 面实拍，链内平铺使用）。    *)
(*  对标: 衔接状态图「组合终形回接」任务项；lnw_wgap_geo        *)
(*        （2^{n+3}，池内保留不改动）的改进替代；lna_supply_rem'（装配件    *)
(*        §5/§8）上界肢的 θ 预算接入与「锐权衰减」腿承载。                  *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（QeqT/QleT'/QltT/sigT/Or 面   *)
(*        real_eq/real_lt/real_le）；Qeq/Qle/Qlt 支撑件仅推理面使用；       *)
(*        QleT' 目标换形全走 lnt_leT'_eq_l/r 与 qeq_leT' 传送（0 次 Qeq     *)
(*        rewrite 进 Id 面目标）；Z 层尾账用 Z.mul_le_mono_nonneg(r) 手工   *)
(*        合成免三变元积 nia；文尾 Print Assumptions 全 Closed＋独立提取    *)
(*        闭合（四件套）。                                                 *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q        *)
(*        vo_local_world_unified_0930 ""（独占沙箱池 ln2_theta2/，链序      *)
(*        tail_bound→numer_int→sharp_weight→ireal→reorder→assembly→        *)
(*        theta_upper→本件；单进程串行）。                          *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import Ln2Bridge.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex RealIdentity.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_sharp_weight.
Require Import abl_ln2_ireal.
Require Import abl_ln2_reorder.
Require Import abl_ln2_assembly.
Require Import abl_ln2_theta_upper.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 real 常值比较微桥（②θ 预算过 real 面的承载件）                        *)
(* ============================================================ *)

(** 常值实数相等：Qeq a b ⟹ real_eq (real_const a) (real_const b)
    （real_eq 的 eps/N 全称面：N:=0，逐点 |a−b|==0<eps）。 *)
Lemma lnr2_const_eq : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H eps Heps. exists 0%nat. intros n Hn.
  change (projT1 (real_const a) n) with a.
  change (projT1 (real_const b) n) with b.
  apply Qlt_to_QltT. apply (lnr_qlt_transfer_l (Qabs (a - b))%Q 0%Q eps).
  - assert (E : (a - b)%Q == 0%Q) by (setoid_rewrite H; ring).
    apply (Qeq_trans (Qabs (a - b))%Q (Qabs 0%Q) 0%Q).
    + apply Qabs_wd. exact E.
    + unfold Qabs. reflexivity.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(** 常值实数严格序：Qlt a b ⟹ real_lt (real_const a) (real_const b)
    （eps := (b−a)/2 的显式配方，N:=0）。 *)
Lemma lnr2_const_lt : forall a b : Q, Qlt a b -> real_lt (real_const a) (real_const b).
Proof.
  intros a b Hab.
  assert (H0 : Qlt 0 (b - a)%Q).
  { pose proof (proj2 (Qplus_lt_r a b (Qopp a)) Hab) as Ht.
    apply (lnr_qlt_transfer_l 0%Q (Qopp a + a)%Q (b - a)%Q).
    - apply Qeq_sym. ring.
    - apply (lnr_qlt_transfer_r (Qopp a + a)%Q (Qopp a + b)%Q (b - a)%Q Ht).
      ring. }
  assert (H1 : Qlt ((b - a) * (1 # 2))%Q (b - a)%Q).
  { apply (lnr_qlt_transfer_r ((b - a) * (1 # 2))%Q ((b - a) * (1 # 1))%Q
             (b - a)%Q).
    - apply (lnr_qmult_lt_compat_l (1 # 2)%Q (1 # 1)%Q (b - a)%Q H0).
      unfold Qlt. cbn [Qnum Qden]. lia.
    - ring. }
  assert (H2 : Qlt 0 ((b - a) * (1 # 2))%Q).
  { apply (lnr_qlt_transfer_r 0%Q ((1 # 2) * (b - a))%Q
             ((b - a) * (1 # 2))%Q).
    - apply (lnr_qlt_transfer_l 0%Q (0 * (b - a))%Q
               ((1 # 2) * (b - a))%Q).
      + apply Qeq_sym. ring.
      + apply Qmult_lt_compat_r.
        * exact H0.
        * unfold Qlt. cbn [Qnum Qden]. lia.
    - ring. }
  exists ((b - a) * (1 # 2))%Q. split.
  - apply Qlt_to_QltT. exact H2.
  - exists 0%nat. intros n Hn.
    change (projT1 (real_const b) n) with b.
    change (projT1 (real_const a) n) with a.
    apply Qlt_to_QltT. exact H1.
Qed.

(** 常值实数序：Qle a b ⟹ real_le (real_const a) (real_const b)
    （real_le 的 Or 编码按 Qlt_le_dec 劈分：严格走 lt、互走 eq）。 *)
Lemma lnr2_const_le : forall a b : Q, Qle a b -> real_le (real_const a) (real_const b).
Proof.
  intros a b Hab.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - left. apply lnr2_const_lt. exact Hlt.
  - right. apply lnr2_const_eq. apply Qle_antisym; [exact Hab | exact Hge].
Qed.

(* ============================================================ *)
(* §① lnw 链常数更新：C 从 2^{n+3} 改进替代为 2^{n+2}（同窗同率）           *)
(* ============================================================ *)

(** 替代名替代终形（与 lnw_wgap_geo 同窗同签名、C 减半）：1 ≤ n、2n ≤ M+1 ⟹
    尾隙 ≤ 2^{n+2}·(3/4)^{SM−2n}——DH 件 lnt2_wgap_geo_quarter 的 lnw 链面
    替代名（statements 逐字同形，exact 闭合；池内 lnw_wgap_geo 原样保留）。 *)
Theorem lnr2_wgap_geo : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof. exact lnt2_wgap_geo_quarter. Qed.

(** 2 幂单调原子：2^{n+2} ≤ 2^{n+3}（q_pow_succ 尾展开＋(1#1)·X 定义性 X
    换形经 lnt_leT'_eq_r 传送、qleT'_mult_compat_r 配 2^{n+2} 正性与 1≤2；
    旧形保留为推论的两处公共核）。 *)
Lemma lnr2_pow2_step : forall n : nat,
  QleT' (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))
        (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))).
Proof.
  intro n.
  apply (lnt_leT'_eq_r (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))
          ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))
          (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n))))).
  - apply Qeq_sym. apply q_pow_succ.
  - apply (lnt_leT'_eq_l ((1 # 1)%Q
                           * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))%Q
            (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))
            ((2 # 1)%Q * q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))).
    + ring.
    + apply (qleT'_mult_compat_r (1 # 1)%Q (2 # 1)%Q
               (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))).
      * apply Qle_to_QleT'. apply Qlt_le_weak. apply lnt_pow2_pos.
      * apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

(** 旧形保留为推论·加法隙形：lnw_wgap_geo 原语句（2^{n+3}）由改进替代形
    经 2^{n+2}≤2^{n+3} 单调闭合——旧使用面全数可用，改进为纯收紧。 *)
Theorem lnr2_wgap_geo_legacy : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
       + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
  - apply lnr2_wgap_geo; assumption.
  - apply qleT'_plus_compat; [apply qleT'_refl |].
    apply (qleT'_mult_compat_r
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n))))
             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
             (lnt_pow_pos_le (Datatypes.S M - 2 * n))
             (lnr2_pow2_step n)).
Qed.

(** 锐权面尾隙·半常数版（lnf_wtail_geo 的改进替代）：1 ≤ n、2n ≤ M+1 ⟹
    Σ_{i<d} w(n,M+1+i) ≤ 2^{n+2}·(3/4)^{SM−2n}——使用 lnr2_wgap_geo 经
    DA 通用相消件 lnf_range_gap_cancel（前缀不等式相消读出）。 *)
Theorem lnr2_wtail_geo : forall (n M d : nat),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
Proof.
  intros n M d Hn HM.
  apply (lnf_range_gap_cancel (fun k => lnw_wterm n k) M d).
  apply lnr2_wgap_geo; assumption.
Qed.

(** 旧形保留为推论·尾隙形：lnf_wtail_geo 原语句（2^{n+3}）由半常数版
    经 lnr2_pow2_step 单调闭合——DA 换序机旧锚位可直换新锚。 *)
Theorem lnr2_wtail_geo_legacy : forall (n M d : nat),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
Proof.
  intros n M d Hn HM.
  apply qleT'_trans with
    ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
  - apply lnr2_wtail_geo; assumption.
  - apply (qleT'_mult_compat_r
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n)))
             (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n))))
             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
             (lnt_pow_pos_le (Datatypes.S M - 2 * n))
             (lnr2_pow2_step n)).
Qed.

(** 锐权面换序误差肢·半常数版（lnf_wgap_limb 的改进替代）：Σ_j b_j·
    (锐权尾隙) ≤ (Σb)·2^{n+2}·(3/4)^{SM−2n}——lnf_sum_scale_r 吸收 Σb＋
    lnf_tail_transport 逐支传送（E 支为与 j 无关的半常数几何档）。 *)
Theorem lnr2_wgap_limb : forall (n J M d : nat) (b : nat -> Q),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  (forall j : nat, (j < J)%nat -> QleT' 0 (b j)) ->
  QleT' (sum_upto J (fun j => (b j
                      * sum_upto d (fun i => lnw_wterm n
                                                    (M + Datatypes.S i)))%Q))
        ((sum_upto J b)
         * (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n J M d b Hn HM Hb.
  apply (lnt_leT'_eq_r
    (sum_upto J (fun j => (b j
                   * sum_upto d (fun i => lnw_wterm n
                                                 (M + Datatypes.S i)))%Q))
    (sum_upto J (fun j => (b j
                   * (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q))
    ((sum_upto J b)
     * (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
        * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q).
  - apply lnf_sum_scale_r.
  - apply (lnf_tail_transport b
             (fun j => sum_upto d (fun i => lnw_wterm n
                                                   (M + Datatypes.S i)))
             (fun j => (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                        * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)
             J Hb).
    intros j Hj. apply lnr2_wtail_geo; assumption.
Qed.

(** 数值锚①（替代名实例）：lna_theta_mod 命名槽定义性钉点 = 4/5
    （vm_compute 判定）。 *)
Theorem lnr2_theta_mod_anchor : QeqT lna_theta_mod (4 # 5)%Q.
Proof. vm_compute. reflexivity. Qed.

(** 数值锚②（半常数实例）：n=3、M=6=2n 带内，新常数 2^{5}·(3/4)^{7−6}
    = 24（旧形 2^{6}·(3/4) = 48 的一半）——vm_compute 判定。 *)
Theorem lnr2_C_quarter_anchor :
  QeqT (24 # 1)%Q (q_pow (2 # 1)%Q 5 * q_pow (3 # 4)%Q 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(** 数值锚③（带内逐点）：w(3,7) ≤ 24——新常数在 n=3、M=6 带内点的
    逐点体现（旧使用面同点上限 48，减半即纯收紧）——vm_compute 判定。 *)
Theorem lnr2_wtail3_anchor : QleT' (lnw_wterm 3 7) (24 # 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §② θ 组合肢接入 lna_supply_rem' 装配（命名槽预算＋上界肢使用桥）         *)
(* ============================================================ *)

(** θ 预算在装配命名槽：4ⁿ·(7/40)ⁿ ≤ θⁿ，θ := lna_theta_mod（=4/5，
    §4 装配命名肢）——DH 件 lnt2_theta_budget 的命名槽直投（lna_theta_mod
    定义性可转换，exact 闭合）。 *)
Theorem lnr2_theta_budget_rem : forall n : nat,
  QleT' (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n)%Q (q_pow lna_theta_mod n)%Q.
Proof. exact lnt2_theta_budget. Qed.

(** 上界肢使用桥（预算面接入）：若线对象 |A_n·X−B_n| 已被预算面
    4ⁿ·(7/40)ⁿ 约束（L_n·I'_n 预算的 real 面供给——S6 恒等式腿到货形），
    则经 lnr2_const_le（Q 层 lnt2_theta_budget 的 real 面提升）与
    real_le_trans 得装配上界肢 ln2b_line_upper lna_Amod lna_Bmod
    lna_theta_mod——θ 组合肢自此接入 lna_supply_rem' 的使用面。 *)
Theorem lnr2_rem_upper_of_budget :
  (forall n : nat, real_le (ln2b_line lna_Amod lna_Bmod n)
                     (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
  ln2b_line_upper lna_Amod lna_Bmod lna_theta_mod.
Proof.
  intro Hb. intro n.
  apply (real_le_trans (ln2b_line lna_Amod lna_Bmod n)
          (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))
          (real_const (q_pow lna_theta_mod n))).
  - apply Hb.
  - apply lnr2_const_le. apply QleT'_to_Qle. apply lnr2_theta_budget_rem.
Qed.

(** 两肢装配 hook：下界肢如实悬置（载体条件 clo≤|A·X−B|，候 S6 恒等式腿，
    禁虚报）；上界肢由 θ 预算面经使用桥接入——lna_supply_rem' 的 B 侧
    （lna_Bmod 实填）两段式装配在 θ 组合肢半边的分步承载。 *)
Theorem lnr2_supply_rem_theta_hook :
  ln2b_line_lower lna_Amod lna_Bmod lna_clo_mod ->
  (forall n : nat, real_le (ln2b_line lna_Amod lna_Bmod n)
                     (real_const (q_pow (4 # 1)%Q n * q_pow (7 # 40)%Q n))) ->
  lna_supply_rem'.
Proof.
  intros Hlo Hb. apply lna_supply_rem'_assemble.
  split; [exact Hlo | apply lnr2_rem_upper_of_budget; exact Hb].
Qed.

(* ============================================================ *)
(* §②+ 锐权衰减消失引擎（装配诚实边界「锐权衰减」腿·半常数承载）           *)
(* ============================================================ *)

(** 半常数几何模量消失：QltT 0 eps ⟹ ∃N，∀M≥N，2^{n+2}·(3/4)^{SM−2n}<eps
    且窗口 2n≤M+1 同时供给——显式配方 N:=2n+4·2^{n+2}·den(eps)。
    链（照 lnr_vanish 同构、常数 2^{p+1}→2^{n+2} 换档）：
    g ≤ 2^{n+2}·3/(E+3) < 2^{n+2}·3/(X+3) < eps（E:=SM−2n ≥ X+1，
    X:=4·2^{n+2}·pd；末步交叉乘 3A·pd < pn·(4A·pd+3) 经
    Z.mul_le_mono_nonneg(r) 手工合成，免三变元积 nia）。 *)
Theorem lnr2_wgapbound_vanish : forall (n : nat) (eps : Q), QltT 0 eps ->
  sigT (fun N : nat => forall M : nat, (N <= M)%nat ->
    And ((2 * n <= M + 1)%nat)
        (QltT ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q) eps)).
Proof.
  intros n [pn pd] Heps.
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (2 * n + (4 * 2 ^ Datatypes.S (Datatypes.S n)
                     * Z.to_nat (Z.pos pd)))%nat.
  intros M Hm.
  assert (HE : (4 * 2 ^ Datatypes.S (Datatypes.S n) * Z.to_nat (Z.pos pd) + 1
                <= Datatypes.S M - 2 * n)%nat) by lia.
  split.
  { lia. }
  assert (HA1 : (0 < Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))%Z).
  { apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S (Datatypes.S n)))).
    assert (Hg := lnt_pow2_ge1 (Datatypes.S (Datatypes.S n))). lia. }
  assert (HApos : Qlt 0 ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) # 1)%Q))
    by (apply rx_Qlt_Z1; exact HA1).
  assert (HAw : (1 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))%Z) by lia.
  assert (HZK : (Z.of_nat (4 * 2 ^ Datatypes.S (Datatypes.S n)
                           * Z.to_nat (Z.pos pd))
                = 4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) * Z.pos pd)%Z).
  { rewrite (Nat2Z.inj_mul (4 * 2 ^ Datatypes.S (Datatypes.S n))
              (Z.to_nat (Z.pos pd))).
    rewrite (Z2Nat.id (Z.pos pd)) by lia.
    rewrite (Nat2Z.inj_mul 4 (2 ^ Datatypes.S (Datatypes.S n))). lia. }
  apply Qlt_to_QltT. rewrite lnt_qpow_Zofnat.
  apply (Qlt_trans _ ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) # 1)%Q
                      * ((3 # 1)%Q / ((Z.of_nat (4 * 2 ^ Datatypes.S
                                            (Datatypes.S n)
                                            * Z.to_nat (Z.pos pd)) + 3) # 1)%Q))%Q).
  - apply (Qle_lt_trans _ ((Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) # 1)%Q
                           * ((3 # 1)%Q / ((Z.of_nat (Datatypes.S M - 2 * n)
                                              + 3) # 1)%Q))%Q).
    + apply lnt_Qmult_le_compat_l.
      * apply Qlt_le_weak. exact HApos.
      * apply lnr_q34_pow_le3.
    + apply lnr_qmult_lt_compat_l.
      * exact HApos.
      * apply lnr_qdivint_antitone.
        -- lia.
        -- lia.
        -- lia.
  - apply (lnr_q3divz_lt (Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)))
            (Z.of_nat (4 * 2 ^ Datatypes.S (Datatypes.S n)
                       * Z.to_nat (Z.pos pd)) + 3)%Z
            pn pd).
    + exact HA1.
    + lia.
    + exact Hpn.
    + rewrite HZK.
      assert (Hlow : (Z.of_nat (2 ^ Datatypes.S (Datatypes.S n)) * 3 * Z.pos pd
                      < 4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                          * Z.pos pd + 3)%Z).
      { assert (Hap : (0 <= Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                         * Z.pos pd)%Z)
          by (apply Z.mul_nonneg_nonneg; lia).
        nia. }
      assert (Hmono : (4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                         * Z.pos pd + 3
                       <= pn * (4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                                  * Z.pos pd + 3))%Z).
      { apply (Z.le_trans (4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                             * Z.pos pd + 3)%Z
                (1 * (4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                       * Z.pos pd + 3))%Z
                (pn * (4 * Z.of_nat (2 ^ Datatypes.S (Datatypes.S n))
                        * Z.pos pd + 3))%Z).
        - rewrite Z.mul_1_l. apply Z.le_refl.
        - apply Z.mul_le_mono_nonneg_r; lia. }
      exact (Z.lt_le_trans _ _ _ Hlow Hmono).
Qed.

(** 锐权衰减消失引擎（w 级数尾隙的 Archimedean 证书）：1 ≤ n、QltT 0 eps
    ⟹ ∃N，∀M≥N、∀d，Σ_{i<d} w(n,M+1+i) < eps——半常数尾隙界
    （lnr2_wtail_geo）与模量消失（lnr2_wgapbound_vanish）的合成；
    装配件 §8 诚实边界所列「锐权衰减」腿在本常数下的承载面。 *)
Theorem lnr2_wvanish : forall (n : nat) (eps : Q),
  (1 <= n)%nat -> QltT 0 eps ->
  sigT (fun N : nat => forall (M d : nat), (N <= M)%nat ->
    QltT (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i))) eps).
Proof.
  intros n eps Hn Heps.
  destruct (lnr2_wgapbound_vanish n eps Heps) as [N Hv].
  exists N. intros M d Hm. destruct (Hv M Hm) as [Hwin Hlt].
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S n))
                          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)).
  - apply QleT'_to_Qle. apply lnr2_wtail_geo; assumption.
  - apply QltT_to_Qlt. exact Hlt.
Qed.

(* ============================================================ *)
(* §D 假设审计与独立提取（born-green 四件套闭合位）                          *)
(* ============================================================ *)

Print Assumptions lnr2_const_eq.
Print Assumptions lnr2_const_lt.
Print Assumptions lnr2_const_le.
Print Assumptions lnr2_wgap_geo.
Print Assumptions lnr2_pow2_step.
Print Assumptions lnr2_wgap_geo_legacy.
Print Assumptions lnr2_wtail_geo.
Print Assumptions lnr2_wtail_geo_legacy.
Print Assumptions lnr2_wgap_limb.
Print Assumptions lnr2_theta_mod_anchor.
Print Assumptions lnr2_C_quarter_anchor.
Print Assumptions lnr2_wtail3_anchor.
Print Assumptions lnr2_theta_budget_rem.
Print Assumptions lnr2_rem_upper_of_budget.
Print Assumptions lnr2_supply_rem_theta_hook.
Print Assumptions lnr2_wgapbound_vanish.
Print Assumptions lnr2_wvanish.

From Stdlib Require Import Extraction.
Separate Extraction lnr2_theta_budget_rem lnr2_wgap_geo lnr2_wtail_geo
  lnr2_wgap_limb lnr2_wgapbound_vanish lnr2_wvanish lnr2_const_le
  lnr2_rem_upper_of_budget lnr2_supply_rem_theta_hook.
