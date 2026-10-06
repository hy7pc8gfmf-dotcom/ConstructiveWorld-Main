(* ===================================================================== *)
(*  abl_ln2_reorder_assembly.v —— ln2 无理性链·Ireal 载体校正装配件           *)
(*  （ln2 载体重定向装配二段）                                   *)
(*  使命: 就前件重大发现——BH 载体错位已判定（机器分离锚 1/2≠1/6：            *)
(*        无权族 lnr_psum（闭形 (2^n−1)/n）≠ I_n 真身面 |2^{n+1}q̃_n·ln2−r_n|）,*)
(*        把 Ireal 装配重定向到真族 lnf_bterm（Beta 加权=C(n+k,n)/2^k·        *)
(*        B(n+k+1,n+1)，其级数和=c_n·ln2−r_n 即 I_n）并接入 DA 换序肢，        *)
(*        完成路线③(ⅲ) 的载体校正装配。四层:                                  *)
(*        ①载体重定向：真族部分和 lns_bsum（Σ_{k≤M} lnf_bterm）＋头读出/      *)
(*          范围劈分/单调性＋首项 1/6 锚＋旧载体分离锚（订正注记的机器取证：   *)
(*          lns_bsum 1 0 = 1/6 ≠ 1/2 = lnr_psum 1 0，BH 旧载体位就此作废）；  *)
(*        ②换序肢接入（真族版，全经 DA 泛型机）：两参矩形换序 lns_bswap_rect  *)
(*          （lnf_fubini_T 在 lnf_bterm 处实例）＋BV 系数×真族矩形换序        *)
(*          lns_bv_bswap（lnf_swap_scale 实例，lnf_bv_pole_swap 的真族兄弟）  *)
(*          ＋数值锚；                                                       *)
(*        ③真族尾界（本件新数学闭合）：阶乘支配 nat 引理 lns_fact_dom          *)
(*          （2(k+1)·n!·(n+k)! ≤ (2n+k+1)!，1 ≤ n，归纳+nia）⟹ Q 桥逐点支配  *)
(*          lns_bdom（lnf_bterm n k ≤ lnt_pterm n k）⟹ 真族尾界两形           *)
(*          lns_btail_pterm4（≤ 4·u(n,SM)，消 AP lnt_pterm_tail）与           *)
(*          lns_btail_geo（≤ 2^{n+1}(3/4)^{SM−2n}，消 DA lnf_pole_tail_gap） *)
(*          ＋换序误差肢 lns_bgap_limb（lnf_tail_transport 传送+Σb 吸收，      *)
(*          lnf_wgap_limb 的真族兄弟）；                                     *)
(*        ④腿重定向（BH 挂点按真族重述并条件闭合）：                          *)
(*          lns_identity_leg_bterm_transfer——ri_identity_leg 的正确迁移形    *)
(*          改锚于真族载体（fun p => lnr_Ireal_pack (lns_bsum p) (Cb p)），   *)
(*          Cauchy 见证 Cb 作显式参数位（构造义务登记见下）；迁移经 real_eq_    *)
(*          trans 两个合取肢直闭——不再穿 lnr_Ireal（旧迁移形的载体位即错位根，      *)
(*          ①分离锚已机器否证该路线）。                                     *)
(*  ★ 响亮申报勘录（余结构差登记，禁虚报）:                                *)
(*        ① lns_bsum 的 Cauchy 见证未构造（Cb 参数位显式悬置）：配方=经        *)
(*           lns_btail_pterm4 得隙 ≤ 4·u(n,SM)，u ≤ 2^{n−1}/(SM+1)          *)
(*           （lnt_bkC_le_pow2 桥）多项式衰减 Archimedean 配方 N:=…——        *)
(*           下片工单（lnr_cauchy 同构重排，预算超限未入本片）；              *)
(*        ② ri_identity_leg 真族载体版的全闭合（real_eq 到 ri_lineabs）      *)
(*           需 Padé 代数恒等式「Σ_k lnf_bterm n k = c_n·ln2 − r_n」的       *)
(*           有限 M 形（换序+尾+闭式合一）——campaign 级余件，本件以②③       *)
(*           承载其换序肢与尾界面，恒等肢登记候件；                          *)
(*        ③ j < n 支（负幂支有理常数）语义归位为对接件义务（同款登记）。   *)
(*  依赖: Stdlib QArith/Arith(Arith.Factorial:fact)/ZArith/Lia；S01_BaseRing   *)
(*        S02_CauchyComplete S03_QExp；PolyIntegral PadeErrorIntegral         *)
(*        BeukersLists BeukersVariant PintMono；PsQReindex RealIdentity；     *)
(*        池内拷贝链                                                          *)
(*        abl_ln2_tail_bound（AP）→ abl_ln2_sharp_weight（CO）→              *)
(*        abl_ln2_ireal（BH）→ abl_ln2_reorder（DA）→ 本件。                  *)
(*  对标: 真族 lnf_bterm 与泛型换序机四件（库内换序恒等式件）；         *)
(*        迁移件 lnr_identity_leg_transfer 挂点与      *)
(*        lnr_psum 载体（旧载体订正面）；     *)
(*        AE 报告 §3 子件(c)「有限 M 级换序恒等式＋尾项控制走柯西胶水」；      *)
(*        BT 报告 路线③(ⅲ) 第三级；AP lnt_pterm_tail/lnt_sum_le；            *)
(*        CO lnw_wgap_limb 吸收形；E621 W1 免展平判据（nat 指标转世）。       *)
(*  构造性: 全件 Qed、零承认；Set 语句主形全 QeqT/QleT'/real_eq（Qeq/Qle     *)
(*        仅 Prop 推理面，BH/DA 件同款纪律）；nat 归纳引理零公理；可提取      *)
(*        （文尾 Separate Extraction）；文尾 Print Assumptions 全 Closed。   *)
(*  编译配方: source <Live>/toolchain/env.sh && rocq c -native-compiler no   *)
(*        -Q <world>/vo_local_world_unified_0930 ""（独占沙箱池              *)
(*        ln2_rassembly/，道闸≤1；同池链序 tail_bound → sharp_weight →       *)
(*        ireal → reorder → 本件）。工艺注记: Qeq 桥一律 setoid_rewrite      *)
(*        （plain rewrite 不识别 Qeq 关系，DA/池件同款）；nat_scope 下算式    *)
(*        显式 %Q/%nat 标注。                                               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Arith.Factorial ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import PolyIntegral PadeErrorIntegral BeukersLists BeukersVariant PintMono.
Require Import PsQReindex RealIdentity.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_sharp_weight.
Require Import abl_ln2_ireal.
Require Import abl_ln2_reorder.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 载体重定向：真族（Beta 加权）部分和                                       *)
(* ============================================================ *)

(* ★ 真族载体：lns_bsum p M := Σ_{k<S M} lnf_bterm p k——BH 载体 lnr_psum     *)
(*    （无权族 Σ lnt_pterm）的校正位。其级数极限=c_n·ln2−r_n 即 I_n 真身。    *)
Definition lns_bsum (p M : nat) : Q := sum_upto (Datatypes.S M) (lnf_bterm p).

(* 逐项非负（单调性的原子；lnf_bterm_pos 的 Qle 面） *)
Lemma lns_bterm_Qle0 : forall p k : nat, Qle 0 (lnf_bterm p k).
Proof. intros p k. apply Qlt_le_weak. apply lnf_bterm_pos. Qed.

(* 头读出：S_0 = b(p,0) = B(p+1,p+1) *)
Lemma lns_bsum_head : forall p : nat, lns_bsum p 0 == lnf_bterm p 0.
Proof.
  intro p. unfold lns_bsum. cbn [sum_upto]. ring.
Qed.

(* 范围劈分（柯西胶水的输入面；lnt_sum_range 泛型直连） *)
Theorem lns_bsum_range : forall (p M d : nat),
  lns_bsum p (M + d) == lns_bsum p M
    + sum_upto d (fun i : nat => lnf_bterm p (M + Datatypes.S i))%Q.
Proof. intros p M d. exact (lnt_sum_range d M (lnf_bterm p)). Qed.

(* 部分和单调：m ≤ k ⟹ S_m ≤ S_k（lnr_psum_mono 的真族转世） *)
Lemma lns_bsum_mono : forall p m k : nat,
  (m <= k)%nat -> Qle (lns_bsum p m) (lns_bsum p k).
Proof.
  intros p m k H.
  assert (Hk : (k = m + (k - m))%nat) by lia.
  remember (k - m)%nat as d eqn:Hd.
  subst k. clear Hd H.
  induction d as [| d IH].
  - replace (m + 0) with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d) with (Datatypes.S (m + d)) by lia.
    unfold lns_bsum in IH |- *. cbn [sum_upto].
    apply (Qle_trans _ (sum_upto (m + d) (lnf_bterm p)
                        + lnf_bterm p (m + d))%Q).
    + exact IH.
    + apply (Qle_trans _ (sum_upto (m + d) (lnf_bterm p)
                          + lnf_bterm p (m + d) + 0)%Q).
      * apply qeq_le. ring.
      * exact (Qplus_le_compat
                 (sum_upto (m + d) (lnf_bterm p) + lnf_bterm p (m + d))%Q
                 (sum_upto (m + d) (lnf_bterm p) + lnf_bterm p (m + d))%Q
                 0%Q (lnf_bterm p (Datatypes.S (m + d)))
                 (Qle_refl _)
                 (lns_bterm_Qle0 p (Datatypes.S (m + d)))).
Qed.

(* 数值锚①（真族首项）：lns_bsum 1 0 = B(2,2) = 1/6（vs 旧载体 1/2） *)
Theorem lns_bsum10_anchor : QeqT (lns_bsum 1 0) (1 # 6)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 数值锚②（真族前两项）：1/6 + 1/12 = 1/4 *)
Theorem lns_bsum11_anchor : QeqT (lns_bsum 1 1) (1 # 4)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ★ 订正注记的机器取证（BH 旧载体位作废锚）：真族头项 ≠ 旧载体头项
（1/6 ≠ 1/2——分离锚 lnf_sep_carrier_bterm 在装配配位的重述：
   旧迁移形「穿 lnr_Ireal」的载体位由此判定不可用） *)
Theorem lns_sep_old_carrier : Not (QeqT (lns_bsum 1 0) (lnr_psum 1 0)).
Proof.
  intro H.
  assert (Heq : (lns_bsum 1 0)%Q == (lnr_psum 1 0)%Q)
    by (apply qeqT_imp_qeq; exact H).
  vm_compute in Heq. discriminate Heq.
Qed.

(* ============================================================ *)
(* §B 换序肢接入（真族版，全经 DA 泛型机）                                      *)
(* ============================================================ *)

(* ★ 真族矩形换序（DA lnf_fubini_T 在 lnf_bterm 处的实例——换序恒等式
   对真族成立的 Fubini 基形） *)
Theorem lns_bswap_rect : forall (M N : nat),
  QeqT (sum_upto M (fun i => sum_upto N (fun j => lnf_bterm i j)))
       (sum_upto N (fun j => sum_upto M (fun i => lnf_bterm i j))).
Proof. intros M N. exact (lnf_fubini_T M N (fun i j => lnf_bterm i j)). Qed.

(* ★ BV 系数×真族矩形换序（DA lnf_swap_scale 实例——lnf_bv_pole_swap 的
   真族兄弟）：Laurent 指标 j∈[0,J) × 极点截断 k∈[0,M)，系数驻外、
   真族驻内；j<n 支语义归位为对接件义务（头注勘录③），恒等式本身
   对任意族成立。 *)
Theorem lns_bv_bswap : forall (n J M : nat),
  sum_upto J (fun j => (bv_c n j * sum_upto M (fun k => lnf_bterm (j - n) k))%Q)
  == sum_upto M (fun k => sum_upto J (fun j => (bv_c n j * lnf_bterm (j - n) k)%Q)).
Proof.
  intros n J M.
  apply (lnf_swap_scale J M (fun j => bv_c n j)
           (fun j k => lnf_bterm (j - n) k)).
Qed.

(* 数值锚③（真族 BV 换序）：n=1、J=3、M=2 矩形 vm_compute 判定 *)
Theorem lns_bv_bswap_anchor :
  QeqT (sum_upto 3 (fun j => (bv_c 1 j * sum_upto 2 (fun k => lnf_bterm (j - 1) k))%Q))
       (sum_upto 2 (fun k => sum_upto 3 (fun j => (bv_c 1 j * lnf_bterm (j - 1) k)%Q))).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §C 真族尾界（本件新数学闭合）：阶乘支配 ⟹ 两形尾隙                           *)
(* ============================================================ *)

(* fact 阶乘步进（定义性；显式重写用，避免 cbn 过度归约破坏语法对形） *)
Lemma lns_fact_succ : forall m : nat,
  fact (Datatypes.S m) = Datatypes.S m * fact m.
Proof. intro m. reflexivity. Qed.

(* ★ nat 核（新数学①）：2(k+1)·n!·(n+k)! ≤ (2n+k+1)!（1 ≤ n）。
   证法=对 n 归纳（底 0 矛盾消）；步阶按整体指标分两案：
   指标 1（底阶代数 2(k+1) ≤ (k+2)(k+3)）与指标 ≥ 2
   （IH 与 (n+2)(n+k+2) ≤ (2n+k+3)(2n+k+2) 的乘法单调合成）。 *)
Lemma lns_fact_dom : forall n k : nat,
  (1 <= n)%nat ->
  (2 * Datatypes.S k * fact n * fact (n + k)
     <= fact (2 * n + k + 1))%nat.
Proof.
  intros n k Hn. revert Hn. induction n as [| n IH]; intro Hn.
  - lia.
  - destruct n as [| n'].
    + (* 底阶：整体指标 = 1 *)
      replace (Datatypes.S 0 + k) with (Datatypes.S k) by lia.
      replace (2 * Datatypes.S 0 + k + 1)
        with (Datatypes.S (Datatypes.S (Datatypes.S k))) by lia.
      rewrite (lns_fact_succ 0), (lns_fact_succ k).
      rewrite (lns_fact_succ (Datatypes.S (Datatypes.S k))),
              (lns_fact_succ (Datatypes.S k)), (lns_fact_succ k).
      assert (E3 : Datatypes.S 0 * fact 0 = 1) by reflexivity.
      rewrite E3.
      assert (Hb : (2 * Datatypes.S k
                    <= Datatypes.S (Datatypes.S k)
                       * Datatypes.S (Datatypes.S (Datatypes.S k)))%nat) by nia.
      assert (E0 : (2 * Datatypes.S k * 1 * (Datatypes.S k * fact k)
                    = (2 * Datatypes.S k) * (Datatypes.S k * fact k))%nat) by ring.
      assert (E0' : (Datatypes.S (Datatypes.S (Datatypes.S k))
                     * (Datatypes.S (Datatypes.S k) * (Datatypes.S k * fact k))
                     = (Datatypes.S (Datatypes.S k)
                        * Datatypes.S (Datatypes.S (Datatypes.S k)))
                       * (Datatypes.S k * fact k))%nat) by ring.
      rewrite E0, E0'.
      apply Nat.mul_le_mono_r. exact Hb.
    + (* 步阶：整体指标 = S (S n')，IH 在指标 S n'（≥ 1）适用 *)
      replace (Datatypes.S (Datatypes.S n') + k)
        with (Datatypes.S (Datatypes.S n' + k)) by lia.
      replace (2 * Datatypes.S (Datatypes.S n') + k + 1)
        with (Datatypes.S (Datatypes.S (2 * Datatypes.S n' + k + 1))) by lia.
      rewrite (lns_fact_succ (Datatypes.S n')),
              (lns_fact_succ (Datatypes.S n' + k)),
              (lns_fact_succ (Datatypes.S (2 * Datatypes.S n' + k + 1))),
              (lns_fact_succ (2 * Datatypes.S n' + k + 1)).
      assert (IHk : (2 * Datatypes.S k * fact (Datatypes.S n')
                     * fact (Datatypes.S n' + k)
                     <= fact (2 * Datatypes.S n' + k + 1))%nat)
        by (apply IH; lia).
      assert (Haux : (Datatypes.S (Datatypes.S n')
                      * Datatypes.S (Datatypes.S n' + k)
                      <= Datatypes.S (Datatypes.S (2 * Datatypes.S n' + k + 1))
                         * Datatypes.S (2 * Datatypes.S n' + k + 1))%nat) by nia.
      assert (E1 : (2 * Datatypes.S k
                    * (Datatypes.S (Datatypes.S n') * fact (Datatypes.S n'))
                    * (Datatypes.S (Datatypes.S n' + k)
                       * fact (Datatypes.S n' + k))
                    = (2 * Datatypes.S k * fact (Datatypes.S n')
                       * fact (Datatypes.S n' + k))
                      * (Datatypes.S (Datatypes.S n')
                         * Datatypes.S (Datatypes.S n' + k)))%nat) by ring.
      assert (E2 : (Datatypes.S (Datatypes.S (2 * Datatypes.S n' + k + 1))
                    * (Datatypes.S (2 * Datatypes.S n' + k + 1)
                       * fact (2 * Datatypes.S n' + k + 1))
                    = fact (2 * Datatypes.S n' + k + 1)
                      * (Datatypes.S (Datatypes.S (2 * Datatypes.S n' + k + 1))
                         * Datatypes.S (2 * Datatypes.S n' + k + 1)))%nat) by ring.
      rewrite E1, E2.
      exact (Nat.mul_le_mono _ _ _ _ IHk Haux).
Qed.

(* q_fact 的 Z.of_nat 阶乘桥（Qeq 面） *)
Lemma lns_qfact_Zofnat : forall m : nat, q_fact m == (Z.of_nat (fact m) # 1)%Q.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - cbn [q_fact]. rewrite IH.
    change (fact (Datatypes.S m)) with (Datatypes.S m * fact m)%nat.
    rewrite Nat2Z.inj_mul.
    unfold Qeq, Qmult. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* 分数交叉乘判据（Prop 面）：0 < b、0 < d 且 a·d ≤ c·b ⟹ a/b ≤ c/d
   （Qdiv 展开后的 Qinv 形；正消元经 lnt_qle_mul_cancel_r） *)
Lemma lns_qdiv_le : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qle (a * d) (c * b) -> Qle (a * Qinv b) (c * Qinv d).
Proof.
  intros a b c d Hb Hd H.
  assert (Eb : (Qinv b * b)%Q == 1%Q) by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Hb).
  assert (Ed : (Qinv d * d)%Q == 1%Q) by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Hd).
  assert (E1 : (a * Qinv b) * (b * d) == a * d).
  { apply (Qeq_trans _ ((a * d) * (Qinv b * b))%Q).
    - ring.
    - rewrite Eb. ring. }
  assert (E2 : (c * Qinv d) * (b * d) == c * b).
  { apply (Qeq_trans _ ((c * b) * (Qinv d * d))%Q).
    - ring.
    - rewrite Ed. ring. }
  apply (lnt_qle_mul_cancel_r (a * Qinv b)%Q (c * Qinv d)%Q (b * d)%Q).
  - apply Qmult_lt_0_compat; assumption.
  - setoid_rewrite E1. setoid_rewrite E2. exact H.
Qed.

(* ★ Q 桥（新数学②）：真族逐项支配——lnf_bterm n k ≤ lnt_pterm n k（1 ≤ n）。
   两分数积先 Qeq 归形为单分数（Eshape：Qinv 合并的 setoid 面），q_fact/q_pow
   桥为 Qmake 字面量后，交叉乘判据（lns_qdiv_le），核=lns_fact_dom 的 Z 版。 *)
Theorem lns_bdom : forall n k : nat,
  (1 <= n)%nat -> QleT' (lnf_bterm n k) (lnt_pterm n k).
Proof.
  intros n k Hn.
  apply Qle_to_QleT'.
  unfold lnf_bterm, lnt_pterm, Qdiv.
  assert (Eshape : ((Z.of_nat (bkC (n + k) n) # 1) * Qinv (q_pow (2 # 1)%Q k))
                   * ((q_fact n * q_fact (n + k))
                      * Qinv (q_fact (2 * n + k + 1)))
                   == ((Z.of_nat (bkC (n + k) n) # 1)
                       * (q_fact n * q_fact (n + k)))
                      * Qinv (q_pow (2 # 1)%Q k * q_fact (2 * n + k + 1))).
  { setoid_rewrite Qinv_mult_distr. ring. }
  setoid_rewrite Eshape.
  setoid_rewrite lnt_qpow_Zofnat.
  setoid_rewrite lns_qfact_Zofnat.
  apply (lns_qdiv_le _ _ _ _).
  - (* 0 < b＝2^k·(2n+k+1)! 的 Qmake 积 *)
    apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1.
      apply (proj1 (Nat2Z.inj_lt 0 (2 ^ k))).
      pose proof (lnt_pow2_ge1 k). lia.
    + apply rx_Qlt_Z1. apply (proj1 (Nat2Z.inj_lt 0 (fact (2 * n + k + 1)))).
      apply Nat.neq_0_lt_0. apply fact_neq_0.
  - (* 0 < d＝(k+1)·2^{k+1} 的积 *)
    apply Qmult_lt_0_compat.
    + apply rx_Qlt_Z1. lia.
    + apply rx_Qlt_Z1.
      apply (proj1 (Nat2Z.inj_lt 0 (2 ^ Datatypes.S k))).
      pose proof (lnt_pow2_ge1 (Datatypes.S k)). lia.
  - (* 交叉乘 Z 核：a·d ≤ c·b＝(bkC·p2)·(2·Sk·fn·fnk) ≤ (bkC·p2)·f23
       （＝lns_fact_dom 不等式乘非负因子 bkC·p2，手工合成免 nia 搜索） *)
    assert (Hc0 : (Z.of_nat (2 * Datatypes.S k * fact n * fact (n + k))
                   <= Z.of_nat (fact (2 * n + k + 1)))%Z).
    { apply Nat2Z.inj_le. apply lns_fact_dom. exact Hn. }
    rewrite !Nat2Z.inj_mul in Hc0.
    assert (Hnn : (0 <= Z.of_nat (2 * Datatypes.S k * fact n * fact (n + k)))%Z)
      by (apply (proj1 (Nat2Z.inj_le 0
             (2 * Datatypes.S k * fact n * fact (n + k)))); lia).
    rewrite !Nat2Z.inj_mul in Hnn.
    unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    change (Z.of_nat (2 ^ Datatypes.S k)) with (Z.of_nat (2 * 2 ^ k)).
    rewrite Nat2Z.inj_mul.
    rewrite !Z.mul_1_r.
    assert (Hbp : (0 <= Z.of_nat (bkC (n + k) n) * Z.of_nat (2 ^ k))%Z)
      by (apply Z.mul_nonneg_nonneg; apply Nat2Z.is_nonneg).
    assert (Eg : (Z.of_nat (bkC (n + k) n)
                  * (Z.of_nat (fact n) * Z.of_nat (fact (n + k)))
                  * (Z.of_nat (Datatypes.S k)
                     * (Z.of_nat 2 * Z.of_nat (2 ^ k)))
                  = (Z.of_nat (bkC (n + k) n) * Z.of_nat (2 ^ k))
                    * (Z.of_nat 2 * Z.of_nat (Datatypes.S k)
                       * Z.of_nat (fact n) * Z.of_nat (fact (n + k))))%Z) by ring.
    assert (Eg' : (Z.of_nat (bkC (n + k) n)
                  * (Z.of_nat (2 ^ k) * Z.of_nat (fact (2 * n + k + 1)))
                  = (Z.of_nat (bkC (n + k) n) * Z.of_nat (2 ^ k))
                    * Z.of_nat (fact (2 * n + k + 1)))%Z) by ring.
    rewrite Eg, Eg'.
    apply Z.mul_le_mono_nonneg.
    + exact Hbp.
    + apply Z.le_refl.
    + exact Hnn.
    + exact Hc0.
Qed.

(* ★ 真族尾界形一（4·u 形）：Σ_{i<d} b(n,M+1+i) ≤ 4·u(n,SM)——
   经 lns_bdom 逐项支配＋AP lnt_pterm_tail（窗口 2n ≤ M+4） *)
Theorem lns_btail_pterm4 : forall (n M d : nat),
  (1 <= n)%nat -> (2 * n <= M + 4)%nat ->
  QleT' (sum_upto d (fun i : nat => lnf_bterm n (M + Datatypes.S i)))
        ((4 # 1)%Q * lnt_pterm n (Datatypes.S M))%Q.
Proof.
  intros n M d Hn HM.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))).
  - apply QleT'_to_Qle. apply lnt_sum_le. intros i Hi. apply lns_bdom. exact Hn.
  - apply QleT'_to_Qle. apply lnt_pterm_tail. exact HM.
Qed.

(* ★ 真族尾界形二（几何形）：Σ_{i<d} b(n,M+1+i) ≤ 2^{n+1}·(3/4)^{SM−2n}——
   经 lns_bdom＋DA lnf_pole_tail_gap（窗口 1 ≤ n、2n ≤ M+1） *)
Theorem lns_btail_geo : forall (n M d : nat),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  QleT' (sum_upto d (fun i : nat => lnf_bterm n (M + Datatypes.S i)))
        ((q_pow (2 # 1)%Q (Datatypes.S n)
          * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q).
Proof.
  intros n M d Hn HM.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (sum_upto d (fun i : nat => lnt_pterm n (M + Datatypes.S i)))).
  - apply QleT'_to_Qle. apply lnt_sum_le. intros i Hi. apply lns_bdom. exact Hn.
  - apply QleT'_to_Qle. apply lnf_pole_tail_gap; assumption.
Qed.

(* ============================================================ *)
(* §D 换序误差肢（真族传送+Σb 吸收）                                            *)
(* ============================================================ *)

(* ★ 真族换序误差肢（lnf_wgap_limb 的真族兄弟）：Σ_j b_j·(真族尾隙)
   ≤ (Σ_j b_j)·2^{n+1}·(3/4)^{SM−2n}——DA lnf_tail_transport 传送
   lns_btail_geo，Σb 吸收经 lnf_sum_scale_r。 *)
Theorem lns_bgap_limb : forall (n J M d : nat) (b : nat -> Q),
  (1 <= n)%nat -> (2 * n <= M + 1)%nat ->
  (forall j : nat, (j < J)%nat -> QleT' 0 (b j)) ->
  QleT' (sum_upto J (fun j => (b j
                      * sum_upto d (fun i : nat => lnf_bterm n
                                                    (M + Datatypes.S i)))%Q))
        ((sum_upto J b)
         * (q_pow (2 # 1)%Q (Datatypes.S n)
            * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n J M d b Hn HM Hb.
  apply (lnt_leT'_eq_r
    (sum_upto J (fun j => (b j
                   * sum_upto d (fun i : nat => lnf_bterm n
                                                 (M + Datatypes.S i)))%Q))
    (sum_upto J (fun j => (b j
                   * (q_pow (2 # 1)%Q (Datatypes.S n)
                      * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q))
    ((sum_upto J b)
     * (q_pow (2 # 1)%Q (Datatypes.S n)
        * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q).
  - apply lnf_sum_scale_r.
  - apply (lnf_tail_transport b
             (fun j => sum_upto d (fun i : nat => lnf_bterm n
                                                   (M + Datatypes.S i)))
             (fun j => (q_pow (2 # 1)%Q (Datatypes.S n)
                        * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)
             J Hb).
    intros j Hj. apply lns_btail_geo; assumption.
Qed.

(* ============================================================ *)
(* §E 腿重定向：BH 挂点按真族重述并条件闭合                                     *)
(* ============================================================ *)

(* ★ 腿重定向件：ri_identity_leg 的正确迁移形改锚于真族载体——
   载体位 = fun p => lnr_Ireal_pack (lns_bsum p) (Cb p)（Beta 加权版
   Ireal_n），Cauchy 见证 Cb 作显式参数位（头注勘录①：构造义务登记）。
   迁移经 real_eq_trans 两个合取肢直闭——不穿 lnr_Ireal（旧迁移形载体位错位
   已由 lns_sep_old_carrier 机器否证）。BH lnr_identity_leg_transfer
   的同构重排，判定结论的载体校正版。 *)
Theorem lns_identity_leg_bterm_transfer : forall (I : ri_Iface)
    (Cb : forall p : nat, cauchy (lns_bsum p)),
  (forall p : nat, real_eq (I p) (lnr_Ireal_pack (lns_bsum p) (Cb p))) ->
  ri_identity_leg (fun p => lnr_Ireal_pack (lns_bsum p) (Cb p)) ->
  ri_identity_leg I.
Proof.
  intros I Cb HI Hleg n.
  apply (real_eq_trans (I n) (lnr_Ireal_pack (lns_bsum n) (Cb n)) (ri_lineabs n)).
  - apply HI.
  - apply Hleg.
Qed.

(* 真族载体定义件（组装面读出：包装不改变逐点读数——lnr_Ireal 同款引理） *)
Definition lns_Ibreal (Cb : forall p : nat, cauchy (lns_bsum p)) (p : nat) : Real :=
  lnr_Ireal_pack (lns_bsum p) (Cb p).

Lemma lns_Ibreal_proj : forall (Cb : forall p : nat, cauchy (lns_bsum p))
    (p k : nat), projT1 (lns_Ibreal Cb p) k == lns_bsum p k.
Proof. intros Cb p k. reflexivity. Qed.

(* ============================================================ *)
(* 可提取出口（Set 层 witness 面）                                             *)
(* ============================================================ *)

Separate Extraction lns_bsum.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。              *)
(* ============================================================ *)

Print Assumptions lns_bsum_range.
Print Assumptions lns_bsum_mono.
Print Assumptions lns_bdom.
Print Assumptions lns_btail_pterm4.
Print Assumptions lns_btail_geo.
Print Assumptions lns_bgap_limb.
Print Assumptions lns_bv_bswap.
Print Assumptions lns_bswap_rect.
Print Assumptions lns_identity_leg_bterm_transfer.
Print Assumptions lns_sep_old_carrier.
Print Assumptions lns_bsum10_anchor.
Print Assumptions lns_bsum11_anchor.
Print Assumptions lns_bv_bswap_anchor.
