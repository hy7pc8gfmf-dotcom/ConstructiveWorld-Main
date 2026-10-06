(* ============================================================ *)
(* abl_Pr_factgrowth_bridge.v —— 素数域第 7 件：LW0FactGrowth 桥接件   *)
(* 模块名：abl_Pr_factgrowth_bridge                                   *)
(* 数学使命：同事塔 LW0FactGrowth（n! ≥ (n/2)^(n/2) 半数底幂下界＋      *)
(*   (10/3)^n ≤ n! 双族压制，Q 层 QleT' 承载）跨线桥接进本地素数域，    *)
(*   交付三组真使用：①增长 race 件 pfb_pow2_pred_le_fact——lw0 主定理   *)
(*   使用出的底 2 版本本上界 2^(n-1) ≤ n!（n ≥ 8），并经换基恒等式       *)
(*   pfb_pow2_double_eq（4^m == 2^{2m}，与本地 HansonLcm hl_pow4 的     *)
(*   nat 层同型恒等式对拍）落下；②Bertrand 搜索器使用件 pfb_search_race  *)
(*   ——DR 件 pbr_scan_some 的命中证把搜索器出口位 p（7 ≤ n 命中则       *)
(*   8 ≤ p）馈入①，数值实例 pfb_search_race_10 以 DR 件实测命中         *)
(*   pbr_search_10 = Some 11 导出 2^10 ≤ 11!，零 vm_compute 纯推导；    *)
(*   ③对拍互哺件 pfb_lcm_interlock／pfb_binom8_interlock——本地 Hanson   *)
(*   线（nat 层 L(n) ≤ n! 与 C(2n,n) ≤ 4^n）经公共地面件               *)
(*   pfb_q_fact_eq_fact（q_fact n == lw0_q_of_nat (fact n)，两线阶乘     *)
(*   在 Q 层判定同一）升到 lw0 阶乘所在的公共地面，n=8 单点两线同点      *)
(*   互洽。此为登记在册的 Erdős 二项式系数路线解锁件：其核心引理         *)
(*   （C(2n,n) 素数幂分析）所需 n! 增长界自此在本地可引。               *)
(* 依赖清单：S02_CauchyComplete（QleT' 判定与双向桥）＋S03_QExp          *)
(*   （q_fact/q_pow）＋LW0FactGrowth（桥接源，池内拷贝编译）＋           *)
(*   HansonLcm（对拍件：hl_lcm_le_fact/hl_binom/hl_le_t 系，统一缓存    *)
(*   根供）＋abl_Pr_bertrand（DR 件：pbr_scan_some/pbr_search_10，       *)
(*   其依赖 abl_Pr_core_01/abl_Pr_enum_02 链编于 prime_bern 池）＋      *)
(*   纯 Stdlib（QArith/Arith/Arith.Factorial/ZArith/Lia/Extraction）。   *)
(* 对标：lw0_fact_lower_growth（同事原件主定理，本件只使用不重证）；      *)
(*   HansonLcm hl_pow4/hl_central_binom_le/hl_lcm_le_fact（nat 层对拍   *)
(*   线）；本地先例 pbr_scan_some（等式前提＋析取三分式使用形）。         *)
(* 构造性注记：主语句面全部 Set 载体（QleT'），标题四件                  *)
(*   （pfb_pow2_pred_le_fact／pfb_search_race／pfb_lcm_interlock／       *)
(*   pfb_binom8_interlock）零悬置假设、零新立公理；等式前提位           *)
(*   （pbr_search n = Some p）为 DR 件 pbr_scan_some 同型先例，属        *)
(*   条件使用形；全件零 not／~／<> 记号、零经典逻辑、零承认；            *)
(*   pfb_pow2_double_eq／pfb_q_of_nat_mul／pfb_q_fact_eq_fact 皆         *)
(*   Qeq 定义层等式可提取；文末 Separate Extraction＋Print Assumptions   *)
(*   取证面，Obj.magic 计数零为交付判据之一。                            *)
(* 编译配方（链编次序：prime_bern 池三件先行，本池两件随后）：            *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/       *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&     *)
(*   nice -19 rocq c -native-compiler no -Q                              *)
(*   /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""*)
(*   -Q ../prime_bern "" -Q . "" abl_Pr_factgrowth_bridge.v              *)
(*   （LW0FactGrowth.v 以同配方去 ../prime_bern 段先编于本池。）          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith Arith.Arith Arith.Factorial ZArith.ZArith Lia.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0FactGrowth.
Require Import HansonLcm.
Require Import abl_Pr_bertrand.

(* ================= §1 公共地面件：nat 像与两线阶乘判定 ================= *)

(* nat ≤ 的有理像提升（使用 lw0_q_of_nat_le_add）。 *)
Lemma pfb_q_of_nat_le : forall a b : nat, (a <= b)%nat ->
  QleT' (lw0_q_of_nat a) (lw0_q_of_nat b).
Proof.
  intros a b H.
  replace b with (a + (b - a))%nat by lia.
  apply lw0_q_of_nat_le_add.
Qed.

(* 有理像保乘：nat 乘入像 == 像相乘（Qeq 定义层等式）。 *)
Lemma pfb_q_of_nat_mul : forall a b : nat,
  lw0_q_of_nat (a * b)%nat == lw0_q_of_nat a * lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qmult, Qeq.
  cbn [Qnum Qden Z.mul Pos.mul].
  rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 两线阶乘判定：Q 层 q_fact 与 nat 层 fact 的有理像逐点同一。
   证明策略：lw0_q_fact_step 步进 × pfb_q_of_nat_mul 保乘 ×
   fact (S n) = S n · fact n 的定义性展开，归纳闭合。 *)
Lemma pfb_q_fact_eq_fact : forall n : nat, q_fact n == lw0_q_of_nat (fact n).
Proof.
  intro n. induction n as [| n IH].
  - reflexivity.
  - rewrite lw0_q_fact_step. rewrite IH.
    rewrite <- pfb_q_of_nat_mul.
    change (lw0_q_of_nat (S n * fact n)%nat) with (lw0_q_of_nat (fact (S n))).
    reflexivity.
Qed.

(* ================= §2 增长 race：底 2 版本（lw0 主定理真使用） ============ *)

(* 换基恒等式：4^m == 2^{2m}（Q 层；与本地 HansonLcm hl_pow4 的 nat 层
   4^n = 2^{2n} 对拍——同一恒等式两线各层各证）。 *)
Lemma pfb_pow2_double_eq : forall m : nat,
  q_pow (4 # 1)%Q m == q_pow (2 # 1)%Q (2 * m)%nat.
Proof.
  intro m. induction m as [| m IH].
  - reflexivity.
  - rewrite q_pow_succ.
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    rewrite !q_pow_succ. rewrite IH. ring.
Qed.

(** 增长 race 主件（lw0 真使用）：对每个 n ≥ 8，2^(n-1) ≤ n!。
    证明策略：按 Nat.odd 分族——奇族 n = 2m+1：2^(n-1) = 2^{2m} == 4^m ≤
    m^m（底单调，4 ≤ m）≤ n!（lw0_fact_lower_growth）；偶族 n = 2m：
    2^(n-1) ≤ 2^{2m} == 4^m ≤ m^m ≤ (2m)!（lw0_pow_half_le_fact_double）。
    全链每一环都是 lw0 增长界的使用位。 *)
Lemma pfb_pow2_pred_le_fact : forall n : nat, (8 <= n)%nat ->
  QleT' (q_pow (2 # 1)%Q (Nat.pred n)) (q_fact n).
Proof.
  intros n Hn. pose proof (Nat.div2_odd n) as Hd.
  destruct (Nat.odd n) eqn:Hodd.
  - (* 奇数族：n = 2m+1，m ≥ 4。降 Qle 面后整链推理（lw0 同款工法）。 *)
    cbn [Nat.b2n] in Hd. set (m := Nat.div2 n) in *.
    assert (Hm4 : (4 <= m)%nat) by lia.
    replace (Nat.pred n) with (2 * m)%nat by lia.
    apply Qle_to_QleT'.
    rewrite <- pfb_pow2_double_eq.
    apply (Qle_trans _ (q_pow (lw0_q_of_nat m) m)).
    + apply QleT'_to_Qle. apply lw0_q_pow_mono_base.
      * vm_compute. reflexivity.
      * apply (pfb_q_of_nat_le 4 m). exact Hm4.
    + (* lw0 主定理使用位：m^m ≤ n!（n = 2m+1 时 m = n/2 直取） *)
      apply QleT'_to_Qle. exact (lw0_fact_lower_growth n).
  - (* 偶数族：n = 2m，m ≥ 4。同法降 Qle 面。 *)
    cbn [Nat.b2n] in Hd. rewrite Nat.add_0_r in Hd.
    set (m := Nat.div2 n) in *.
    assert (Hm4 : (4 <= m)%nat) by lia.
    replace n with (2 * m)%nat by lia.
    apply Qle_to_QleT'.
    apply (Qle_trans _ (q_pow (2 # 1)%Q (Datatypes.S (Nat.pred (2 * m))))).
    + apply QleT'_to_Qle. apply lw0_q_pow_le_succ_pow. vm_compute. reflexivity.
    + replace (Datatypes.S (Nat.pred (2 * m)))%nat with (2 * m)%nat by lia.
      apply (Qle_trans _ (q_pow (lw0_q_of_nat m) m)).
      * rewrite <- pfb_pow2_double_eq.
        apply QleT'_to_Qle. apply lw0_q_pow_mono_base.
        -- vm_compute. reflexivity.
        -- apply (pfb_q_of_nat_le 4 m). exact Hm4.
      * apply QleT'_to_Qle. exact (lw0_pow_half_le_fact_double m).
Qed.

(* lw0 线 n=8 对拍单点：4^4 ≤ 8!（lw0_fact_lower_growth 直取，与 §4
   Hanson 线 n=8 单点同位配对——两线中项同为 4^4）。 *)
Lemma pfb_lw0_8_point : QleT' (q_pow (lw0_q_of_nat 4) 4) (q_fact 8).
Proof. exact (lw0_fact_lower_growth 8). Qed.

(* lw0 线 n=24 单点：12^12 ≤ 24!（Q 层 Z 二进制数值面，附加展点）。 *)
Lemma pfb_lw0_24_point : QleT' (q_pow (lw0_q_of_nat 12) 12) (q_fact 24).
Proof. exact (lw0_pow_half_le_fact_double 12). Qed.

(* ================= §3 Bertrand 搜索器使用件（真使用示范） ============== *)

(** 搜索器出口位 race（条件使用形，DR 件 pbr_scan_some 同型先例）：
    DR 件升扫搜索器 pbr_search n 命中 Some p 且 n ≥ 7 时，命中位 p ≥ 8
    馈入增长 race 主件——lw0 增长界在素数域搜索器出口位的实例化。 *)
Lemma pfb_search_race : forall n p : nat,
  pbr_search n = Some p -> (7 <= n)%nat ->
  QleT' (q_pow (2 # 1)%Q (Nat.pred p)) (q_fact p).
Proof.
  intros n p Hhit Hn.
  destruct (pbr_scan_some n n p Hhit) as [Hlt [Hle _]].
  apply pfb_pow2_pred_le_fact. lia.
Qed.

(** 数值实例（零 vm_compute 纯推导）：DR 件实测命中 pbr_search 10 =
    Some 11（pbr_search_10）经使用件导出 2^10 ≤ 11!。 *)
Lemma pfb_search_race_10 : QleT' (q_pow (2 # 1)%Q 10) (q_fact 11).
Proof.
  apply (pfb_search_race 10 11 pbr_search_10). lia.
Qed.

(* ================= §4 Hanson 对拍互哺件（两线增长界共地面） ============ *)

(** 对拍主件：本地 Hanson 线 lcm 上界（nat 层 L(n) ≤ n!）经公共地面件
    pfb_q_fact_eq_fact 升到 lw0 阶乘所在的 Q 层——两线增长界自此同点
    （同一 q_fact n）互洽：lw0 线供 n! 下界，Hanson 线供 L(n) 上界。 *)
Lemma pfb_lcm_interlock : forall n : nat,
  QleT' (lw0_q_of_nat (hl_lcm_upto n)) (q_fact n).
Proof.
  intro n. apply Qle_to_QleT'.
  rewrite (pfb_q_fact_eq_fact n).
  apply QleT'_to_Qle.
  apply pfb_q_of_nat_le. exact (hl_lcm_le_fact n).
Qed.

(** 对拍数值点（n=8 单点两线同点互洽）：Hanson 线 C(8,4) ≤ 4^4 ≤ 8!
    （nat 层 hl_central_binom_le 4 ＋数值闭判定）升 Q 层，与 lw0 线单点
    4^4 ≤ 8!（pfb_lw0_8_point）同点配对——两线中项同为 4^4。
    数值判定注记：nat 层阶乘为一元载体，闭判定点取 8!（40320）而非
    更大点位（24! 一元展开不可行），Q 层点位（pfb_lw0_24_point）不受此限。 *)
Lemma pfb_binom8_interlock : QleT' (lw0_q_of_nat (hl_binom 8 4)) (q_fact 8).
Proof.
  apply Qle_to_QleT'. rewrite (pfb_q_fact_eq_fact 8).
  apply QleT'_to_Qle.
  apply pfb_q_of_nat_le.
  apply (Nat.le_trans (hl_binom 8 4) (4 ^ 4)%nat).
  - apply hl_le_t_to_le. exact (hl_central_binom_le 4).
  - vm_compute. lia.
Qed.

(* ================= §5 提取检验与公理面自审（取证面） ================== *)

(* 提取检验：主语句族 Separate Extraction，提取产物 Obj.magic 计数零
   为交付判据（复核报告附 grep 取证）。 *)

From Stdlib Require Import Extraction.
Separate Extraction pfb_pow2_double_eq pfb_q_fact_eq_fact
  pfb_pow2_pred_le_fact pfb_search_race pfb_search_race_10
  pfb_lcm_interlock pfb_binom8_interlock pfb_lw0_8_point pfb_lw0_24_point.

Print Assumptions pfb_pow2_double_eq.
Print Assumptions pfb_q_fact_eq_fact.
Print Assumptions pfb_pow2_pred_le_fact.
Print Assumptions pfb_search_race.
Print Assumptions pfb_search_race_10.
Print Assumptions pfb_lcm_interlock.
Print Assumptions pfb_binom8_interlock.
Print Assumptions pfb_lw0_8_point.
Print Assumptions pfb_lw0_24_point.
