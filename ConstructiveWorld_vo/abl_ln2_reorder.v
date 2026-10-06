(* ===================================================================== *)
(*  abl_ln2_reorder.v —— ln2 无理性链·有限 M 换序恒等式（ri_identity_leg      *)
(*  本证攻坚·换序恒等式关键件）                                            *)
(*  使命: 闭合挂点 lnr_identity_leg_transfer 背后的路线③(ⅲ)核心——      *)
(*        Ireal_n 求和↔积分换序的离散承载。Pure-quest 裁定（勘验：库无      *)
(*        Real 积分机）：「积分」以 Q 层逐项和容器承载，恒等式=两级有限和     *)
(*        的换序（Fubini 离散形）＋误差肢。三层:                              *)
(*        ①离散 Fubini 泛型：sum_upto 双求和换序 Qeq 泛型（内层归纳法，       *)
(*          E621 W1 免展平判据）＋ QeqT Set 主形 lnf_fubini_T ＋系数外提      *)
(*          换序推论 lnf_swap_scale；                                        *)
(*        ②载体实例化：(n,k) 因子分解 lnf_pterm_core（lnt_pterm n k ==        *)
(*          C(n+k,n)·c_k，c_k 即 ln2 级数第 k+1 步——极点部逐项的换序原子）   *)
(*          与 BV 系数×极点族矩形换序 lnf_bv_pole_swap（Laurent 指标 j×      *)
(*          极点截断 M——A_n·x_M′−B_n 有限恒等式的换序骨架），并经            *)
(*          lnf_reorder_leg_conditional 使用 BH 挂点（同池对接实证）；        *)
(*        ③误差肢：换序尾隙传送器 lnf_tail_transport（逐支界×非负系数——      *)
(*          尾隙界的接入口）＋极点面 lnf_pole_tail_gap/lnf_pole_limb    *)
(*          （使用 AP lnt_gap_geo）＋锐权面终形 lnf_wtail_geo/lnf_wgap_limb  *)
(*          （使用 CO lnw_wgap_geo：尾隙 ≤ 2^{n+3}·(3/4)^{SM−2n} 接入换序    *)
(*          误差肢——指定对接完成）。                                   *)
(*  ★ 响亮申报勘录（实文调形，禁虚报）: BH 载体 lnr_psum（Σ lnt_pterm，     *)
(*        闭形 (2^n−1)/n，n=1 时极限=1）与 ri_lineabs 面（|2^{n+1}q̃_n·ln2−   *)
(*        r_n|，n=1 时 |12ln2−8|≈0.318）两面不等——若相等则 ln2=(3/4)∈Q，     *)
(*        与全役目标自相矛盾。故 ri_identity_leg lnr_Ireal 按现载体为假，     *)
(*        本证须换 Beta 加权族：本件供给 lnf_bterm（= C(n+k,n)/2^k·          *)
(*        B(n+k+1,n+1)，阶乘式经 q_fact；其级数和=2^{n+1}q̃_n·ln2−r_n 即     *)
(*        I_n 真身，n=1 首项 1/6 vs 无权族 1/2 的机器分离锚                  *)
(*        lnf_sep_carrier_bterm）。换序件全部按族泛型构造（对 lnt_pterm/    *)
(*        lnw_wterm/lnf_bterm 同形适用），BH 侧载体调形（lnr_psum 换        *)
(*        lnf_bterm 族并配 Cauchy 见证）为下片义务，登记于卷内勘录。            *)
(*        （换序恒等式件所承）。                           *)
(*  依赖: Stdlib QArith/Arith/ZArith/Lia；S01_BaseRing S02_CauchyComplete    *)
(*        S03_QExp；PolyIntegral PadeErrorIntegral BeukersLists Beukers-    *)
(*        Variant PintMono PsQReindex；池内拷贝链 abl_ln2_tail_bound        *)
(*        （AP 系）→ abl_ln2_sharp_weight（CO 系）→ abl_ln2_ireal（BH 系）。 *)
(*  对标: 「有限 M 换序证 ri_identity_leg 后经迁移件任意取形」；     *)
(*        AE 报告 §3 子件(c)「有限 M 级换序恒等式＋尾项控制走柯西胶水」；    *)
(*        BT 报告 §路线③(ⅲ)（多项式除法＋残数归位＋有限M换序）之第三级；    *)
(*        lnw_wgap_geo 尾隙界；E621 W1 列表 Fubini 免展平内层归纳      *)
(*        判据（nat 指标 sum_upto 同构转世）。                              *)
(*  构造性: 全件 Qed、零承认；Set 语句主形全 QeqT/QleT'（Qeq 泛型仅 Prop     *)
(*        推理面，BH 件同款纪律）；分离锚为 Prop 面 Not 形（fail-loud 取    *)
(*        证）；可提取（文尾 Separate Extraction）；文尾 Print Assumptions  *)
(*        全 Closed。                                                       *)
(*  编译配方: source <Live>/toolchain/env.sh && rocq c -native-compiler no  *)
(*        -Q <world>/vo_local_world_unified_0930 ""（独占沙箱池              *)
(*        ln2_reorder/，道闸≤1；同池链序 tail_bound → sharp_weight →        *)
(*        ireal → 本件）。工艺注记: Open Scope nat_scope 下无期望类型的      *)
(*        fun 体算式不回溯 Scope（首错实录），一律显式 %Q 标注。             *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex RealIdentity.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_sharp_weight.
Require Import abl_ln2_ireal.

Open Scope nat_scope.

(* ============================================================ *)
(* §1 层① 离散 Fubini 泛型（sum_upto 有限双求和换序）                       *)
(*     sum_upto n f = Σ_{i<n} f i（S03 定义件：0 ↦ 0，S ↦ 前和＋末项）      *)
(* ============================================================ *)

(* 求和同延性（Qeq 逐点传送） *)
Lemma lnf_sum_ext : forall (N : nat) (f g : nat -> Q),
  (forall i : nat, f i == g i) -> sum_upto N f == sum_upto N g.
Proof.
  intros N f g H. induction N as [| N IH].
  - reflexivity.
  - cbn [sum_upto]. rewrite IH. rewrite (H N). ring.
Qed.

(* 零函数和 *)
Lemma lnf_sum_zero : forall N : nat, sum_upto N (fun _ : nat => 0%Q) == 0.
Proof.
  induction N as [| N IH].
  - reflexivity.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

(* 内层零和（换序 nil 步的泛型形：内界为 0 时整和为 0） *)
Lemma lnf_sum_zero_gen : forall (N : nat) (f : nat -> nat -> Q),
  sum_upto N (fun j => sum_upto 0 (fun i => f i j)) == 0.
Proof.
  intros N f. induction N as [| N IH].
  - reflexivity.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

(* 和的加法分配 *)
Lemma lnf_sum_plus : forall (N : nat) (f g : nat -> Q),
  sum_upto N (fun i => (f i + g i)%Q) == sum_upto N f + sum_upto N g.
Proof.
  intros N f g. induction N as [| N IH].
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

(* 常数左外提 *)
Lemma lnf_sum_scale_l : forall (N : nat) (c : Q) (f : nat -> Q),
  sum_upto N (fun i => (c * f i)%Q) == c * sum_upto N f.
Proof.
  intros N c f. induction N as [| N IH].
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

(* 常数右外提 *)
Lemma lnf_sum_scale_r : forall (N : nat) (f : nat -> Q) (c : Q),
  sum_upto N (fun i => (f i * c)%Q) == sum_upto N f * c.
Proof.
  intros N f c. induction N as [| N IH].
  - cbn [sum_upto]. ring.
  - cbn [sum_upto]. rewrite IH. ring.
Qed.

(* ★ 层①主件：有限双求和换序（离散 Fubini，Qeq 泛型）。
   证法=内层归纳（E621 W1：免展平——展平+置换在 Set 层死路；
   cons 步=加法分配＋IH，nil 步=零函数和），零新增结构。 *)
Lemma lnf_fubini : forall (M N : nat) (f : nat -> nat -> Q),
  sum_upto M (fun i => sum_upto N (fun j => f i j))
  == sum_upto N (fun j => sum_upto M (fun i => f i j)).
Proof.
  intros M. induction M as [| m IH]; intros N f.
  - change (sum_upto 0 (fun i : nat => sum_upto N (fun j : nat => f i j)))
      with 0%Q.
    apply Qeq_sym. apply lnf_sum_zero_gen.
  - change (sum_upto (Datatypes.S m) (fun i : nat => sum_upto N (fun j : nat => f i j)))
      with (sum_upto m (fun i : nat => sum_upto N (fun j : nat => f i j))
            + sum_upto N (fun j : nat => f m j))%Q.
    transitivity (sum_upto N (fun j : nat => sum_upto m (fun i : nat => f i j))
                  + sum_upto N (fun j : nat => f m j))%Q.
    + rewrite (IH N f). reflexivity.
    + symmetry. apply lnf_sum_plus.
Qed.

(* 层① Set 主形（QeqT——库内 Set 层相等叶子，提取友好） *)
Theorem lnf_fubini_T : forall (M N : nat) (f : nat -> nat -> Q),
  QeqT (sum_upto M (fun i => sum_upto N (fun j => f i j)))
       (sum_upto N (fun j => sum_upto M (fun i => f i j))).
Proof. intros M N f. apply qeq_imp_qeqT. apply lnf_fubini. Qed.

(* 层①推论：系数外提换序——Σ_j c_j·Σ_k g j k == Σ_k Σ_j c_j·g j k
   （换序误差肢的承载形：系数驻外、族驻内） *)
Theorem lnf_swap_scale : forall (J M : nat) (c : nat -> Q) (g : nat -> nat -> Q),
  sum_upto J (fun j => (c j * sum_upto M (fun k => g j k))%Q)
  == sum_upto M (fun k => sum_upto J (fun j => (c j * g j k)%Q)).
Proof.
  intros J M c g.
  transitivity (sum_upto J (fun j => sum_upto M (fun k => (c j * g j k)%Q)))%Q.
  - apply lnf_sum_ext. intro j. symmetry. apply lnf_sum_scale_l.
  - apply lnf_fubini.
Qed.

(* 数值锚①（非平凡见证）：极点族 3×2 矩形换序 vm_compute 判定 *)
Theorem lnf_anchor_fubini :
  QeqT (sum_upto 3 (fun i => sum_upto 2 (fun k => lnt_pterm i k)))
       (sum_upto 2 (fun k => sum_upto 3 (fun i => lnt_pterm i k))).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §2 层② Ireal_n 载体的换序实例化                                          *)
(* ============================================================ *)

(* ln2 级数步长核：c_k = 1/((k+1)·2^{k+1})（= ∫₀¹(t/2)^k dt 的 Q 承载，
   即 ln2i_x 的第 k+1 步——AE §3「极点项逐项积分恰是 ln2i_x 项」的定形） *)
Definition lnf_ln2core (k : nat) : Q :=
  ((1 # 1)%Q / ((Z.of_nat (Datatypes.S k) # 1)
                * q_pow (2 # 1)%Q (Datatypes.S k)))%Q.

(* ★ 换序原子：(n,k) 因子分解——载体项 == 组合因子×步长核。
   极点部逐项（多项式部 Beta 积分＋极点部几何展开）的 Q 层交接点。 *)
Theorem lnf_pterm_core : forall n k : nat,
  QeqT (lnt_pterm n k)
       ((Z.of_nat (bkC (n + k) n) # 1) * lnf_ln2core k)%Q.
Proof.
  intros n k. apply qeq_imp_qeqT.
  unfold lnt_pterm, lnf_ln2core, Qdiv. ring.
Qed.

(* ★ 层②主件：BV 系数×极点族矩形换序——Laurent 指标 j∈[0,J) × 极点截断
   k∈[0,M)。这是 A_n·x_M′−B_n 有限恒等式（AE §3）的换序骨架：
   有限和一侧按 Laurent 支分组、另一侧按极点幂次分组，两侧 Q 层恒等。
   注: j−n 取截减 nat 读法；j<n 支的语义归位（负幂支为有理常数、不入
   几何尾）为对接件义务，换序恒等式本身对任意族成立（Fubini 不挑族）。 *)
Theorem lnf_bv_pole_swap : forall (n J M : nat),
  sum_upto J (fun j => (bv_c n j * sum_upto M (fun k => lnt_pterm (j - n) k))%Q)
  == sum_upto M (fun k => sum_upto J (fun j => (bv_c n j * lnt_pterm (j - n) k)%Q)).
Proof.
  intros n J M.
  apply (lnf_swap_scale J M (fun j => bv_c n j)
           (fun j k => lnt_pterm (j - n) k)).
Qed.

(* 数值锚②（非平凡见证）：BV 系数面 n=1、J=3、M=2 换序 vm_compute 判定 *)
Theorem lnf_anchor_bv_swap :
  QeqT (sum_upto 3 (fun j => (bv_c 1 j * sum_upto 2 (fun k => lnt_pterm (j - 1) k))%Q))
       (sum_upto 2 (fun k => sum_upto 3 (fun j => (bv_c 1 j * lnt_pterm (j - 1) k)%Q))).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 载体部分和的范围劈分（lnr_psum 读出形——柯西胶水的输入面） *)
Theorem lnf_psum_range : forall (n M d : nat),
  lnr_psum n (M + d) == lnr_psum n M
    + sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i))%Q.
Proof. intros n M d. exact (lnt_sum_range d M (lnt_pterm n)). Qed.

(* ★ fail-loud 调形件：Beta 加权真族——I_n = Σ_k C(n+k,n)/2^k·B(n+k+1,n+1)
   的 Q 承载（B 的阶乘式经 q_fact）。BH 载体 lnr_psum 系无权族
   （闭形 (2^n−1)/n ≠ |2^{n+1}q̃_n·ln2−r_n|），勘录见头注与报告。 *)
Definition lnf_bterm (n k : nat) : Q :=
  (((Z.of_nat (bkC (n + k) n) # 1) / q_pow (2 # 1)%Q k) *
   ((q_fact n * q_fact (n + k)) / q_fact (2 * n + k + 1)))%Q.

Theorem lnf_bterm_pos : forall n k : nat, Qlt 0 (lnf_bterm n k).
Proof.
  intros n k. unfold lnf_bterm.
  apply Qmult_lt_0_compat.
  - unfold Qdiv. apply Qmult_lt_0_compat.
    + assert (Hb : 1 <= bkC (n + k) n) by (apply bkC_pos; lia).
      assert (Hz : (0 <= Z.of_nat (bkC (n + k) n))%Z) by apply Nat2Z.is_nonneg.
      unfold Qlt. cbn [Qnum Qden Qmult Pos.mul]. lia.
    + apply Qinv_lt_0_compat. apply lnt_pow2_pos.
  - unfold Qdiv. apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
    + apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* 数值锚③：加权族首项 B(2,2)=1/6（vs 无权族首项 1/2） *)
Theorem lnf_anchor_bterm10 : QeqT (lnf_bterm 1 0) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ★ 分离锚（fail-loud 机器取证）：两族首项不等——BH 载体调形的
   机器级证据（1/2 ≠ 1/6，Qcompare 判 Lt；经 qeqT_imp_qeq 降至 Qeq 的
   Z.eq 面判别——库内 qeqT_imp_qeq 同款判别式纪律） *)
Theorem lnf_sep_carrier_bterm : Not (QeqT (lnt_pterm 1 0) (lnf_bterm 1 0)).
Proof.
  intro H.
  assert (Heq : (lnt_pterm 1 0)%Q == (lnf_bterm 1 0)%Q)
    by (apply qeqT_imp_qeq; exact H).
  vm_compute in Heq. discriminate Heq.
Qed.

(* ★ BH 挂点使用（同池对接实证）：lnr_identity_leg_transfer 的迁移形——
   任意取形 I 一经供得与 lnr_Ireal 的族形 real_eq 与 lnr_Ireal 面的恒等式
   腿，即得 ri_identity_leg I。本件换序机即「腿前提」的制造机（条件形）。 *)
Theorem lnf_reorder_leg_conditional : forall (I : ri_Iface),
  (forall p : nat, real_eq (I p) (lnr_Ireal p)) ->
  ri_identity_leg lnr_Ireal -> ri_identity_leg I.
Proof. intros I HI Hleg. exact (lnr_identity_leg_transfer I HI Hleg). Qed.

(* ============================================================ *)
(* §3 层③ 误差肢：换序尾隙传送器与两族实例                                  *)
(* ============================================================ *)

(* 范围劈分×几何尾隙的相消读出：由前缀不等式 A+B′ ≤ A+G 提取尾隙 B′ ≤ G
   （lnt_leT'_eq_l 传送＋stdlib Qplus_le_r 单步相消——两族尾界共用的通用件；
   注: Qeq 不得 rewrite 进 QleT'（Id 面）假设，BH 件同款坑卡纪律） *)
Lemma lnf_range_gap_cancel : forall (f : nat -> Q) (M d : nat) (G : Q),
  QleT' (sum_upto (Datatypes.S (M + d)) f)
        (sum_upto (Datatypes.S M) f + G)%Q ->
  QleT' (sum_upto d (fun i : nat => f (M + Datatypes.S i))) G.
Proof.
  intros f M d G Hg.
  pose proof (lnt_sum_range d M f) as Hr.
  apply Qle_to_QleT'.
  apply (proj1 (Qplus_le_r
                  (sum_upto d (fun i : nat => f (M + Datatypes.S i))) G
                  (sum_upto (Datatypes.S M) f))).
  exact (QleT'_to_Qle _ _ (lnt_leT'_eq_l _ _ _ Hr Hg)).
Qed.

(* ★ 换序尾隙传送器（层③通用件）：逐支界×非负系数——
   任一尾隙界（lnt_gap_geo / lnw_wgap_geo / 下片 bterm 界）经此
   接入换序误差肢：Σ_j c_j·T_j ≤ Σ_j c_j·E_j。 *)
Theorem lnf_tail_transport : forall (c : nat -> Q) (T E : nat -> Q) (J : nat),
  (forall j : nat, (j < J)%nat -> QleT' 0 (c j)) ->
  (forall j : nat, (j < J)%nat -> QleT' (T j) (E j)) ->
  QleT' (sum_upto J (fun j => (c j * T j)%Q))
        (sum_upto J (fun j => (c j * E j)%Q)).
Proof.
  intros c T E J Hc HE. apply lnt_sum_le. intros i Hi.
  apply qleT'_mult_compat_l.
  - apply Hc. exact Hi.
  - apply HE. exact Hi.
Qed.

(* 极点面尾隙（tail-only 形）：Σ_{i<d} u(n,M+1+i) ≤ 2^{n+1}·(3/4)^{SM−2n}
   （使用 AP lnt_gap_geo 经通用相消件） *)
Theorem lnf_pole_tail_gap : forall (n M d : nat),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  QleT' (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))
        ((q_pow (2 # 1)%Q (Datatypes.S n)
          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
Proof.
  intros n M d Hn HM.
  apply (lnf_range_gap_cancel (fun k => lnt_pterm n k) M d).
  apply lnt_gap_geo; assumption.
Qed.

(* ★ 极点面换序误差肢：BV 系数×极点尾隙的传送实例（使用 lnt_gap_geo）。
   窗前提逐支给出（几何档只对极点支 j≥n+2 生效；j≤n 支为有理常数支、
   无级数尾，归位工单见报告诚实边界）。 *)
Theorem lnf_pole_limb : forall (n J M d : nat) (b : nat -> Q),
  (forall j : nat, (j < J)%nat ->
    (1 <= j - n)%nat /\ (2 * (j - n) <= M + 1)%nat) ->
  (forall j : nat, (j < J)%nat -> QleT' 0 (b j)) ->
  QleT' (sum_upto J (fun j => (b j
                      * sum_upto d (fun i => lnt_pterm (j - n)
                                                    (M + Datatypes.S i)))%Q))
        (sum_upto J (fun j => (b j
                      * (q_pow (2 # 1)%Q (Datatypes.S (j - n))
                         * q_pow (3 # 4)%Q (Datatypes.S M - 2 * (j - n)))%Q)%Q)).
Proof.
  intros n J M d b Hwin Hb.
  apply (lnf_tail_transport b
           (fun j => sum_upto d (fun i => lnt_pterm (j - n)
                                                 (M + Datatypes.S i)))
           (fun j => (q_pow (2 # 1)%Q (Datatypes.S (j - n))
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * (j - n)))%Q)
           J Hb).
  intros j Hj. destruct (Hwin j Hj) as [Ha Hc].
  apply lnf_pole_tail_gap; assumption.
Qed.

(* ★ 锐权面尾隙终形（tail-only 形）：Σ_{i<d} w(n,M+1+i) ≤
2^{n+3}·(3/4)^{SM−2n}——lnw_wgap_geo 前缀形的尾隙读出
（使用 lnw_wgap_geo 经通用相消件；指定对接：该尾隙控制
   接到换序恒等式的误差肢上）。 *)
Theorem lnf_wtail_geo : forall (n M d : nat),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  QleT' (sum_upto d (fun i : nat => lnw_wterm n (M + Datatypes.S i)))
        ((q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
Proof.
  intros n M d Hn HM.
  apply (lnf_range_gap_cancel (fun k => lnw_wterm n k) M d).
  apply lnw_wgap_geo; assumption.
Qed.

(* ★ 锐权面换序误差肢（终形）：Σ_j b_j·(锐权族尾隙) ≤ (Σb)·2^{n+3}·(3/4)^{SM−2n}
   ——系数总和的吸收（bv_c 界）为下片工单，本形已把 CO 尾隙界接入
   换序肢的承载位。 *)
Theorem lnf_wgap_limb : forall (n J M d : nat) (b : nat -> Q),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  (forall j : nat, (j < J)%nat -> QleT' 0 (b j)) ->
  QleT' (sum_upto J (fun j => (b j
                      * sum_upto d (fun i => lnw_wterm n
                                                    (M + Datatypes.S i)))%Q))
        ((sum_upto J b)
         * (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n J M d b Hn HM Hb.
  apply (lnt_leT'_eq_r
    (sum_upto J (fun j => (b j
                   * sum_upto d (fun i => lnw_wterm n
                                                 (M + Datatypes.S i)))%Q))
    (sum_upto J (fun j => (b j
                   * (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q))
    ((sum_upto J b)
     * (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
        * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q).
  - apply lnf_sum_scale_r.
  - apply (lnf_tail_transport b
             (fun j => sum_upto d (fun i => lnw_wterm n
                                                   (M + Datatypes.S i)))
             (fun j => (q_pow (2 # 1)%Q
                          (Datatypes.S (Datatypes.S (Datatypes.S n)))
                        * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)
             J Hb).
    intros j Hj. apply lnf_wtail_geo; assumption.
Qed.

(* ============================================================ *)
(* 可提取闭合（Set 层 witness 面）                                          *)
(* ============================================================ *)

Separate Extraction lnf_ln2core lnf_bterm.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。          *)
(* ============================================================ *)

Print Assumptions lnf_fubini_T.
Print Assumptions lnf_swap_scale.
Print Assumptions lnf_pterm_core.
Print Assumptions lnf_bv_pole_swap.
Print Assumptions lnf_psum_range.
Print Assumptions lnf_bterm_pos.
Print Assumptions lnf_sep_carrier_bterm.
Print Assumptions lnf_reorder_leg_conditional.
Print Assumptions lnf_range_gap_cancel.
Print Assumptions lnf_tail_transport.
Print Assumptions lnf_pole_tail_gap.
Print Assumptions lnf_pole_limb.
Print Assumptions lnf_wtail_geo.
Print Assumptions lnf_wgap_limb.
Print Assumptions lnf_anchor_fubini.
Print Assumptions lnf_anchor_bv_swap.
Print Assumptions lnf_anchor_bterm10.
