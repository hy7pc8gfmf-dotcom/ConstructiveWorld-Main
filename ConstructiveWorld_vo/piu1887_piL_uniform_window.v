(* 五字段指针｜模块：piu1887_piL_uniform_window。使命：pi_L 投影序列 lw0m_xL 的
   统一逃逸窗（escape window）——tdm225 统一窗语句形（u5c_dm_escape_window 的
   dmew_escape_closed_window 窗阶显式面）的 pi_L 对应形。窗阶取显式可计算函数
   n0 := max Nk (pie_modulus (eps * (1 # 10)))，以等词分支 Id n0 〈函数〉钉定；
   在内核窗口前提（QltT 0 eps 且一切 m >= Nk 有 eps < |xL m - q|）下证窗距
   lw0m_e n0 严格小于点距 |q - xL n0|；再经 leibsep_q_kernel 实例化得无条件形，
   n0(q) 成为 q 的项级函数（pie_modulus 与 max 的合成，配合内核闭合件即为
   den(q) 的显式函数）。字面窗阶 den+3 形对 pi_L 数学上不成立（Leibniz 余项率
   1/(2n+1) 使 e(den+3) 与任何 |pi - q| 下界相比恒不逃逸），故取 max/模量合成形。
  依赖：S01_BaseRing（Id/id_refl/NatLe/NatLe_lift）、S02_CauchyComplete（QltT/
   QltT_to_Qlt）、S03_QExp（qltT_trans）、PiEnvelope（pie_modulus/
   pie_modulus_bound/pie_mag_antitone/pie_mag_pos）、LW0MLicBridge（lw0m_e/
   lw0m_xL）、LW0LeibSeparation（leibsep_q_kernel）。
  对标行：UpReqIrrationalCriterion.v :242（lic_escape_window 窗型）；Lw0LeibEscapeAt.v
   （同族存在形先例，本件增补等词钉定与守卫参数化两面）；LW0MLicBridge.v :16/:48
   （统一窗函数与消失模量形本源）；LW0LeibSeparation.v :5452（内核源）；
   PiEnvelope.v :575（pie_modulus 显式模量）。
  构造性注记：零公理零承认（件尾 Print Assumptions 应 Closed）；语句面全 Set 层
   （sigT/And/QltT/Id 均 Set 值，前提位无一 Prop）；证内 Prop（Qlt）仅作推导辅助，
   出口位一律 Qlt_to_QltT 回 Set；主定理收尾为 qltT_trans 合成链（无求解器），
   辅助件 piu1887_vanish_ge 的 Q 线性不等式段以 lra-Q 承担（辅助步，例外册在册
   用法，于此申报）。诚实边界：正距离证书（eps 与 Nk）居前提位，其 den(q) 闭式
   供形由配套内核闭合件提供；leibsep_q_kernel 证内 Niven 多项式机不在本件重复。
  编译配方：coqc -native-compiler no -q -Q <本件目录> "" -Q
   "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import Local.LW0LeibSeparation.

(* ============================================================ *)
(* §0 统一窗阶函数（显式可计算：max 与 pie_modulus 的合成）            *)
(* ============================================================ *)

Definition piu1887_n0 (Nk : nat) (eps : Q) : nat :=
  Nat.max Nk (pie_modulus (eps * (1 # 10))).

(* ============================================================ *)
(* §1 消失面显式模量形（pie_modulus (eps/10) 消解：LW0MLicBridge §2      *)
(*    消失推导的显式模量版，见证阶不再经由不透明量词）                    *)
(* ============================================================ *)

Lemma piu1887_vanish_ge :
  forall (eps : Q) (n : nat),
    QltT 0 eps ->
    (pie_modulus (eps * (1 # 10)) <= n)%nat -> QltT (lw0m_e n) eps.
Proof.
  intros eps n Heps Hn.
  assert (Heps0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hd10 : Qlt 0 (eps * (1 # 10))%Q) by lra.
  pose proof (pie_modulus_bound (eps * (1 # 10))%Q Hd10) as Hb.
  pose proof (pie_mag_pos (pie_modulus (eps * (1 # 10)))) as Hpm.
  assert (Hanti : Qle (pie_mag n) (pie_mag (pie_modulus (eps * (1 # 10)))))
    by (apply pie_mag_antitone; exact Hn).
  unfold lw0m_e. apply Qlt_to_QltT. lra.
Qed.

(* ============================================================ *)
(* §2 统一逃逸窗（守卫参数化形）：内核前提（0 < eps 与一致点距下界）        *)
(*    下，窗阶恰为 piu1887_n0 Nk eps 的见证使命题成立；等词分支由           *)
(*    id_refl 定义性闭合，结论为消失链与内核链的 qltT_trans 合成。         *)
(* ============================================================ *)

Theorem piu1887_piL_escape_window_guarded :
  forall (q eps : Q) (Nk : nat),
    QltT 0 eps ->
    (forall m : nat, NatLe Nk m -> QltT eps (Qabs ((lw0m_xL m - q)%Q))) ->
    sigT (fun n0 : nat =>
      And (Id n0 (piu1887_n0 Nk eps))
          (QltT (lw0m_e n0) (Qabs ((lw0m_xL n0 - q)%Q)))).
Proof.
  intros q eps Nk Heps Hk.
  assert (HleM : (pie_modulus (eps * (1 # 10)) <= piu1887_n0 Nk eps)%nat)
    by (unfold piu1887_n0; apply Nat.le_max_r).
  assert (HleK : NatLe Nk (piu1887_n0 Nk eps))
    by (apply NatLe_lift; unfold piu1887_n0; apply Nat.le_max_l).
  exists (piu1887_n0 Nk eps). split.
  - apply id_refl.
  - apply (qltT_trans _ eps).
    + exact (piu1887_vanish_ge eps _ Heps HleM).
    + exact (Hk _ HleK).
Qed.

(* ============================================================ *)
(* §3 无条件形：经 leibsep_q_kernel 实例化，n0(q) 为 q 的项级函数         *)
(* ============================================================ *)

Definition piu1887_eps_of (q : Q) : Q := projT1 (leibsep_q_kernel q).

Definition piu1887_Nk_of (q : Q) : nat :=
  projT1 (snd (projT2 (leibsep_q_kernel q))).

Definition piu1887_n0_of (q : Q) : nat :=
  piu1887_n0 (piu1887_Nk_of q) (piu1887_eps_of q).

Theorem piu1887_piL_escape_window :
  forall q : Q,
    sigT (fun n0 : nat =>
      And (Id n0 (piu1887_n0_of q))
          (QltT (lw0m_e n0) (Qabs ((lw0m_xL n0 - q)%Q)))).
Proof.
  intros q.
  unfold piu1887_n0_of, piu1887_Nk_of, piu1887_eps_of.
  destruct (leibsep_q_kernel q) as [c [Hc0 [Nk HNk]]].
  exact (piu1887_piL_escape_window_guarded q c Nk Hc0 HNk).
Qed.

(* ============================================================ *)
(* §4 闭式窗口函数实算样例（vm_compute：lw0m_e 5 = 5/11；                 *)
(*    n0 10 (1/100) = max 10 (pie_modulus (1/1000)) = max 10 4001 = 4001） *)
(* ============================================================ *)

Lemma piu1887_sample_e5 : Id (lw0m_e 5) (5 # 11)%Q.
Proof. vm_compute. apply id_refl. Qed.

Lemma piu1887_sample_n0 : Id (piu1887_n0 10 (1 # 100)%Q) 4001%nat.
Proof. vm_compute. apply id_refl. Qed.

Print Assumptions piu1887_vanish_ge.
Print Assumptions piu1887_piL_escape_window_guarded.
Print Assumptions piu1887_piL_escape_window.

Separate Extraction piu1887_n0 piu1887_n0_of piu1887_piL_escape_window.
