(* ===================================================================== *)
(*  abl_ln2_transfer_limb.v —— ln2 无理性链·⑥逐点⟹积分传送/交替裂分肢件    *)
(*  模块名：abl_ln2_transfer_limb.                                        *)
(*  使命: DH §⑥.1 登记的「逐点⟹积分传送/交替裂分」转化肢件，与             *)
(*        BT ③之⑤上界肢配套（ln2 上肢装配前提）。库内无 Real 积分机         *)
(*        （PolyIntegral 头注自认），Pure-quest 裁定：传送件以              *)
(*        BV/CO 有理求和容器语义承载（逐项和形传送，非真积分——与 DP2        *)
(*        IntegMachine 桥的端点泛函代数化、pint 逐项定积分机三面互补，     *)
(*        对拍表见交付报告）。三层：                                       *)
(*        【层1】离散传送泛型（Q 层 sigT/And Set 面）：逐点界 P(k) ≤ B      *)
(*        （∀k<M，Set 面指标见证 lnt3_nlt=Id(Nat.ltb k M) true——S01        *)
(*        NatLe 同族、S06 NatLt 同型自建免重依赖）⟹ 和界 Σ_{k<M}P ≤ M·B    *)
(*        （lnt3_sum_bmax，真归纳）；max 见证形 ΣP ≤ M·P(m0)（And 对偶肢   *)
(*        lnt3_sum_bmax_wit ＋ sigT 见证形 lnt3_sum_bmax_sig——「ΣP ≤      *)
(*        M·max P」的构造性承载：max 以见证索引 m0 与逐点传送函数给出，     *)
(*        无 Prop 存在）。                                                 *)
(*        【层2】lnw/lnt 载体实例化：锐权逐点峰界 lnw_wterm_peak（w ≤ 2^n） *)
(*        传送为部分和容器界 Σ_{k<M}w(n,k) ≤ M·2^n（lnt3_wsum_peak）；基线  *)
(*        u 载体 lnt_pterm 同型（lnt3_usum_peak）；键带逐点终形 w(n,m) ≤    *)
(*        2^n·ρ^{m−2n}（lnt3_wpt_band，2n≤m，纯点界——峰档×lnt2 键带纯      *)
(*        几何率的复合原子）；窗和实例 Σ_{i<d} w(n,M+1+i) ≤ d·2^n·ρ^{SM−2n} *)
(*        （lnt3_wtail_window——「逐点尾隙→和尾隙」的正形实例化，显式计数  *)
(*        d 即层1 M·B 形的直接落点，对照 lnt2_wterm_tail_pure 几何尾形      *)
(*        4·w(n,M+1) 为互异传送面）；层2主定理 lnt3_wsum_band_total：S_{M+d}*)
(*        全容器 ≤ SM·2^n + d·2^n·ρ^{SM−2n}——头窗（峰档传送）＋尾窗（键带  *)
(*        点界传送）的显式合成：纯逐点数据到有理求和容器面（积分面的代数化  *)
(*        承载）的传送，与 lnt2_wgap_geo_quarter 的相对加法隙形互补。       *)
(*        【层3】交替裂分肢（余量闭合）：AE §3.4「交替裂分」递归            *)
(*        1/(1+t) = 1 − t/(1+t) 的 J 步有限容器面代数化——1 == (1+a)·       *)
(*        Σ_{j<J}(−a)^j + (−a)^J（lnt3_asplit_geo，零前提 QeqT）＋沿 Q     *)
(*        标量的逐项和传送形（lnt3_asplit_scaled，SumInvFactEscape 同型    *)
(*        机器的 Q 容器承载）＋数值锚。诚实注：此为代数恒等式面的裂分件，    *)
(*        I'_n 终界（θ^n 面装配）仍为下游缺口，本件不冒领。                 *)
(*  依赖: Stdlib QArith/List/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-    *)
(*        Complete S03_QExp PolyIntegral PadeErrorIntegral BeukersLists     *)
(*        BeukersVariant PintMono PsQReindex；本地链拷贝 abl_ln2_tail_bound *)
(*        abl_ln2_sharp_weight abl_ln2_theta_upper（池内平铺 Require）。    *)
(*  对标: Beukers 1979 ln2 锐权变体上界肢（REV20 论文3 路线⑤）的传送肢；    *)
(*        AE §3.4 预算「(7/40)^n 逐点界到级数和的传送」的容器面承载；        *)
(*        DH §⑥.1/DP 二派完成度图登记缺口的闭合位；与 DP2 端点泛函桥、     *)
(*        pint 逐项定积分机三面互补（对拍表见交付报告）。                    *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（QeqT/QleT'/QltT＋S01 And/    *)
(*        sigT 见证）；指标面 Set 层 lnt3_nlt（Id(Nat.ltb) true），drop/    *)
(*        lift 双桥免 Prop 悬置；新立假设位=0（峰界 1≤n、键带 2n≤m 等前提  *)
(*        均为语句输入参数位的当场消解形，非遗漏假设）；文尾 Print Assumptions*)
(*        全 Closed＋独立提取闭合（四件套）。                               *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&       *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no            *)
(*        -Q <vo_local_world_unified_0930> "" -Q . ""（编译目录=本池，      *)
(*        链序 tail_bound→sharp_weight→theta_upper→本件，道闸≤1 单道串行）。*)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex.
Require Import abl_ln2_tail_bound abl_ln2_sharp_weight abl_ln2_theta_upper.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 工器件：Set 面指标见证、nat 计数缩放核、ρ 幂反单调                    *)
(* ============================================================ *)

(* Set 面指标见证：k < M 的 bool 反射 Id 形（S01 NatLe 同族构造；
   S06 NatLt 同型自建——免 S06 重依赖的池内落地）。 *)
Definition lnt3_nlt (k M : nat) : Set := Id (Nat.ltb k M) true.

Lemma lnt3_nlt_drop : forall k M : nat, lnt3_nlt k M -> (k < M)%nat.
Proof.
  intros k M H. unfold lnt3_nlt in H. destruct (Nat.ltb k M) eqn:E.
  - apply (proj1 (Nat.ltb_lt k M)). exact E.
  - inversion H.
Qed.

Lemma lnt3_nlt_lift : forall k M : nat, (k < M)%nat -> lnt3_nlt k M.
Proof.
  intros k M H. unfold lnt3_nlt. destruct (Nat.ltb k M) eqn:E.
  - apply id_refl.
  - exfalso. apply (proj2 (Nat.ltb_lt k M)) in H. rewrite H in E. discriminate E.
Qed.

(** nat 计数缩放核（层1 M·B 迭代原子）：(S M)#1·B == (M#1)·B + B——
    LW0PiIrrational L3168 配方（Qeq unfold+cbn+Z lia 换形，Qeq 目标内
    rewrite，ring 收尾）。 *)
Lemma lnt3_qscale_succ : forall (M : nat) (B : Q),
  ((Z.of_nat (Datatypes.S M) # 1) * B)%Q == (((Z.of_nat M # 1) * B + B)%Q).
Proof.
  intros M B.
  assert (Hz : (Z.of_nat (Datatypes.S M) # 1)%Q == ((Z.of_nat M # 1)%Q + 1)%Q).
  { assert (Hn : Z.of_nat (Datatypes.S M) = (Z.of_nat M + 1)%Z) by lia.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult]. rewrite Hn. lia. }
  rewrite Hz. ring.
Qed.

(** ρ=3/4 幂指数反单调（0<ρ≤1 带内）：d ≤ e ⟹ ρ^e ≤ ρ^d——
    ρ^{Se} = ρ·ρ^e ≤ 1·ρ^e（0 ≤ ρ^e、ρ ≤ 1，左因子共享单调）。 *)
Lemma lnt3_rho_pow_anti : forall d e : nat, d <= e ->
  QleT' (q_pow (3 # 4)%Q e) (q_pow (3 # 4)%Q d).
Proof.
  intros d e. revert d. induction e as [| e IHe]; intros d Hde.
  - replace d with 0%nat by lia. apply qleT'_refl.
  - destruct (Nat.eq_dec d (Datatypes.S e)) as [Hd | Hd].
    + rewrite Hd. apply qleT'_refl.
    + assert (Hle : d <= e) by lia.
      apply (qleT'_trans (q_pow (3 # 4)%Q (Datatypes.S e))
              ((3 # 4)%Q * q_pow (3 # 4)%Q e)%Q (q_pow (3 # 4)%Q d)).
      * apply lnt_leT'_eq_l with (x := ((3 # 4)%Q * q_pow (3 # 4)%Q e)%Q).
        -- rewrite q_pow_succ. apply Qeq_refl.
        -- apply qleT'_refl.
      * apply (qleT'_trans ((3 # 4)%Q * q_pow (3 # 4)%Q e)%Q
                (q_pow (3 # 4)%Q e) (q_pow (3 # 4)%Q d)).
        -- apply lnt_leT'_eq_r with (y := (1 * q_pow (3 # 4)%Q e)%Q).
           ++ ring.
           ++ apply Qle_to_QleT'. apply Qmult_le_compat_r.
              ** unfold Qle. cbn [Qnum Qden]. lia.
              ** apply QleT'_to_Qle. apply lnt_pow_pos_le.
        -- apply IHe. exact Hle.
Qed.

(* ============================================================ *)
(* §1 层1·离散传送泛型（Q 层 sigT/And Set 面）                            *)
(* ============================================================ *)

(** 主泛型 A（均匀界传送）：逐点 P(k) ≤ B（∀k<M，Set 面指标见证）⟹
    Σ_{k<M} P(k) ≤ M·B——「逐点⟹求和」的最小完备形（真归纳核）。 *)
Theorem lnt3_sum_bmax : forall (M : nat) (P : nat -> Q) (B : Q),
  (forall k : nat, lnt3_nlt k M -> QleT' (P k) B) ->
  QleT' (sum_upto M P) ((Z.of_nat M # 1) * B)%Q.
Proof.
  intros M P B. induction M as [| M IH]; intros Hpt.
  - apply lnt_leT'_eq_r with (y := 0%Q).
    + cbn [Z.of_nat]. ring.
    + cbn [sum_upto]. apply qleT'_refl.
  - cbn [sum_upto].
    apply (qleT'_trans (sum_upto M P + P M)%Q
            ((Z.of_nat M # 1) * B + B)%Q
            ((Z.of_nat (Datatypes.S M) # 1) * B)%Q).
    + apply qleT'_plus_compat.
      * apply IH. intros k Hk. apply Hpt. apply lnt3_nlt_lift.
        pose proof (lnt3_nlt_drop k M Hk). lia.
      * apply Hpt. apply lnt3_nlt_lift. lia.
    + apply qeq_leT'. symmetry. apply lnt3_qscale_succ.
Qed.

(** 主泛型 B（max 见证形·And 对偶）：max 以见证索引 m0<M 与逐点传送
    函数给出（Set 层 And 积载体，无 Prop 存在）⟹ Σ_{k<M} P(k) ≤ M·P(m0)。 *)
Theorem lnt3_sum_bmax_wit : forall (M : nat) (P : nat -> Q) (m0 : nat),
  And (lnt3_nlt m0 M)
      (forall k : nat, lnt3_nlt k M -> QleT' (P k) (P m0)) ->
  QleT' (sum_upto M P) ((Z.of_nat M # 1) * P m0)%Q.
Proof.
  intros M P m0 H. destruct H as [Hm0 Hpt].
  apply lnt3_sum_bmax. intros k Hk. apply Hpt. exact Hk.
Qed.

(** 主泛型 B'（sigT 见证形）：「ΣP ≤ M·max P」的全构造性承载——max 的
    存在性以 sigT 见证（索引 m0 与逐点传送函数的 Set 积）供给，结论亦为
    sigT 见证形（界 B := P(m0)）。 *)
Theorem lnt3_sum_bmax_sig : forall (M : nat) (P : nat -> Q),
  sigT (fun m0 : nat =>
          And (lnt3_nlt m0 M)
              (forall k : nat, lnt3_nlt k M -> QleT' (P k) (P m0))) ->
  sigT (fun B : Q => QleT' (sum_upto M P) ((Z.of_nat M # 1) * B)%Q).
Proof.
  intros M P H. destruct H as [m0 Hm]. destruct Hm as [Hm0 Hpt].
  exists (P m0). apply lnt3_sum_bmax_wit. split.
  - exact Hm0.
  - exact Hpt.
Qed.

(* ============================================================ *)
(* §2 层2·lnw/lnt 载体实例化（锐权逐点尾隙 → 和尾隙）                     *)
(* ============================================================ *)

(** 实例化①（锐权部分和容器界）：1 ≤ n ⟹ Σ_{k<M} w(n,k) ≤ M·2^n——
    逐点峰界 lnw_wterm_peak 经层1泛型的直接传送（有理求和容器面的峰档
    上界）。 *)
Theorem lnt3_wsum_peak : forall (n M : nat), 1 <= n ->
  QleT' (sum_upto M (lnw_wterm n))
        ((Z.of_nat M # 1) * q_pow (2 # 1)%Q n)%Q.
Proof.
  intros n M Hn. apply lnt3_sum_bmax. intros k Hk.
  apply lnw_wterm_peak. exact Hn.
Qed.

(** 实例化②（基线 u 载体同型）：1 ≤ n ⟹ Σ_{k<M} u(n,k) ≤ M·2^{n−1}。 *)
Theorem lnt3_usum_peak : forall (n M : nat), 1 <= n ->
  QleT' (sum_upto M (lnt_pterm n))
        ((Z.of_nat M # 1) * q_pow (2 # 1)%Q (n - 1))%Q.
Proof.
  intros n M Hn. apply lnt3_sum_bmax. intros k Hk.
  apply lnt_pterm_peak. exact Hn.
Qed.

(** 实例化③（键带逐点终形）：1 ≤ n、2n ≤ m ⟹ w(n,m) ≤ 2^n·ρ^{m−2n}
    ——纯逐点面：峰档（2n 处）×键带纯几何率（lnt2_wterm_pow_pure）的
    复合原子，供窗和传送的逐点前提。 *)
Theorem lnt3_wpt_band : forall (n m : nat), 1 <= n -> 2 * n <= m ->
  QleT' (lnw_wterm n m)
        (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (m - 2 * n))%Q.
Proof.
  intros n m Hn Hm.
  assert (Hkey : 2 * n * (2 * n + 2) <= (2 * n + 1) * (2 * n + 5))
    by (apply lnt2_key_of_ge; lia).
  pose proof (lnt2_wterm_pow_pure n (2 * n) (m - 2 * n) Hkey) as Hp.
  replace (2 * n + (m - 2 * n)) with m in Hp by lia.
  apply (qleT'_trans (lnw_wterm n m)
          (lnw_wterm n (2 * n) * q_pow (3 # 4)%Q (m - 2 * n))%Q
          (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (m - 2 * n))%Q).
  - exact Hp.
  - apply (qleT'_mult_compat_r (lnw_wterm n (2 * n)) (q_pow (2 # 1)%Q n)
             (q_pow (3 # 4)%Q (m - 2 * n)) (lnt_pow_pos_le (m - 2 * n))).
    apply lnw_wterm_peak. exact Hn.
Qed.

(** 实例化④（窗和·M·max 形）：1 ≤ n、2n ≤ M+1 ⟹
    Σ_{i<d} w(n,M+1+i) ≤ d·2^n·ρ^{SM−2n}——「逐点尾隙→和尾隙」的正形
    实例化：显式计数 d（层1 M·B 形的直接落点），对照 lnt2_wterm_tail_pure
    几何尾形（4·w(n,M+1)）为互异传送面。 *)
Theorem lnt3_wtail_window : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((Z.of_nat d # 1)
           * (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q.
Proof.
  intros n M d Hn HM. apply lnt3_sum_bmax. intros i Hi.
  assert (Hp2 : QleT' 0 (q_pow (2 # 1)%Q n))
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply lnt_pow2_pos).
  apply (qleT'_trans (lnw_wterm n (M + Datatypes.S i))
          (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (M + Datatypes.S i - 2 * n))%Q
          (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
  - apply lnt3_wpt_band; [exact Hn | lia].
  - apply (qleT'_mult_compat_l
             (q_pow (3 # 4)%Q (M + Datatypes.S i - 2 * n))
             (q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))
             (q_pow (2 # 1)%Q n) Hp2).
    apply lnt3_rho_pow_anti. lia.
Qed.

(** 实例化⑤（层2主定理·全容器传送）：1 ≤ n、2n ≤ M+1 ⟹
    S_{M+d} := Σ_{k≤M+d} w(n,k) ≤ SM·2^n + d·2^n·ρ^{SM−2n}——头窗（峰档
    传送）＋尾窗（键带点界传送）的全容器显式合成：纯逐点数据到有理求和
    容器面（积分面的代数化承载）的传送，与 lnt2_wgap_geo_quarter 的相对
    加法隙形（S_{M+d} ≤ S_M + 2^{n+2}·ρ^{SM−2n}）互补。 *)
Theorem lnt3_wsum_band_total : forall (n M d : nat), 1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (lnw_wterm n))
        ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
         + (Z.of_nat d # 1)
             * (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q.
Proof.
  intros n M d Hn HM.
  apply (lnt_leT'_eq_l
    (sum_upto (Datatypes.S M) (lnw_wterm n)
       + sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))%Q
    (sum_upto (Datatypes.S (M + d)) (lnw_wterm n))
    ((Z.of_nat (Datatypes.S M) # 1) * q_pow (2 # 1)%Q n
     + (Z.of_nat d # 1)
         * (q_pow (2 # 1)%Q n * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n)))%Q).
  - apply Qeq_sym. apply lnt_sum_range.
  - apply qleT'_plus_compat.
    + apply lnt3_wsum_peak. exact Hn.
    + exact (lnt3_wtail_window n M d Hn HM).
Qed.

(** 数值锚（窗和实例）：n=2、M=5、d=3（键带 2n=4 ≤ M+1=6 在带内）：
    Σ_{i<3} w(2,6+i) ≤ 3·4·(9/16) = 27/4——vm_compute 判定。 *)
Theorem lnt3_anchor_wtail : QleT'
  (sum_upto 3 (fun i : nat => lnw_wterm 2 (5 + Datatypes.S i)))
  ((Z.of_nat 3 # 1) * (q_pow (2 # 1)%Q 2 * q_pow (3 # 4)%Q (6 - 4)))%Q.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §3 层3·交替裂分肢（余量闭合）：1/(1+t)=1−t/(1+t) 递归展开的容器面       *)
(* ============================================================ *)

(** 核心（交替几何裂分恒等式·零前提）：1 == (1+a)·Σ_{j<J}(−a)^j + (−a)^J
    ——AE §3.4「交替裂分」递归 1/(1+t) = 1 − t/(1+t) 的 J 步有限代数化
    （SumInvFactEscape 同型机器的 Q 容器承载；精确代数恒等式，无任何
    极限/积分对象——离散化忠实性=恒等式本身，无近似步）。 *)
Theorem lnt3_asplit_geo : forall (J : nat) (a : Q),
  QeqT 1%Q (((1 + a) * sum_upto J (fun j : nat => q_pow (Qopp a) j)
              + q_pow (Qopp a) J)%Q).
Proof.
  intros J a. induction J as [| J IHJ].
  - apply qeq_imp_qeqT. cbn [sum_upto q_pow]. ring.
  - cbn [sum_upto]. apply qeq_imp_qeqT. rewrite q_pow_succ.
    pose proof (qeqT_imp_qeq _ _ IHJ) as Heq.
    apply Qeq_trans with
      (y := ((1 + a) * sum_upto J (fun j : nat => q_pow (Qopp a) j)
              + q_pow (Qopp a) J)%Q).
    + exact Heq.
    + ring.
Qed.

(** 标量传送形：c == (1+a)·Σ_{j<J} c·(−a)^j + c·(−a)^J——裂分恒等式沿
    Q 标量 c 的逐项和面传送（求和容器线性性的使用位）。 *)
Theorem lnt3_asplit_scaled : forall (J : nat) (a c : Q),
  QeqT c%Q (((1 + a) * sum_upto J (fun j : nat => c * q_pow (Qopp a) j)
              + c * q_pow (Qopp a) J)%Q).
Proof.
  intros J a c. induction J as [| J IHJ].
  - apply qeq_imp_qeqT. cbn [sum_upto q_pow]. ring.
  - cbn [sum_upto]. apply qeq_imp_qeqT. rewrite q_pow_succ.
    pose proof (qeqT_imp_qeq _ _ IHJ) as Heq.
    apply Qeq_trans with
      (y := ((1 + a) * sum_upto J (fun j : nat => c * q_pow (Qopp a) j)
              + c * q_pow (Qopp a) J)%Q).
    + exact Heq.
    + ring.
Qed.

(** 数值锚（裂分实例）：J=3、a=1/2：1 == (3/2)·(1 − 1/2 + 1/4) + (−1/8)
    = 9/8 − 1/8（vm_compute 判定）。 *)
Theorem lnt3_asplit_anchor :
  QeqT 1%Q (((1 + (1 # 2)%Q)
               * sum_upto 3 (fun j : nat => q_pow (Qopp (1 # 2)%Q) j)
              + q_pow (Qopp (1 # 2)%Q) 3)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §D 假设审计与独立提取（born-green 四件套闭合位）                          *)
(* ============================================================ *)

Print Assumptions lnt3_nlt_drop.
Print Assumptions lnt3_nlt_lift.
Print Assumptions lnt3_qscale_succ.
Print Assumptions lnt3_rho_pow_anti.
Print Assumptions lnt3_sum_bmax.
Print Assumptions lnt3_sum_bmax_wit.
Print Assumptions lnt3_sum_bmax_sig.
Print Assumptions lnt3_wsum_peak.
Print Assumptions lnt3_usum_peak.
Print Assumptions lnt3_wpt_band.
Print Assumptions lnt3_wtail_window.
Print Assumptions lnt3_wsum_band_total.
Print Assumptions lnt3_anchor_wtail.
Print Assumptions lnt3_asplit_geo.
Print Assumptions lnt3_asplit_scaled.
Print Assumptions lnt3_asplit_anchor.

From Stdlib Require Import Extraction.
Separate Extraction lnt3_nlt_drop lnt3_nlt_lift lnt3_qscale_succ
  lnt3_rho_pow_anti lnt3_sum_bmax lnt3_sum_bmax_wit lnt3_sum_bmax_sig
  lnt3_wsum_peak lnt3_usum_peak lnt3_wpt_band lnt3_wtail_window
  lnt3_wsum_band_total lnt3_anchor_wtail lnt3_asplit_geo
  lnt3_asplit_scaled lnt3_asplit_anchor.
