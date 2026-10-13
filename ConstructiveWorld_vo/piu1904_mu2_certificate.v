(* 五字段指针｜模块：piu1904_mu2_certificate。使命：π 幂率测度框架（LW1PiMeasure）
   的数值证书闭合包装——逐 q 闭式分离证书装填 lw1m_b_cert_face 接口位，统一
   逃逸窗（piu1887_piL_uniform_window）与窗级闭式证书（piu1901 内核闭合件）
   拼合，率阶 μ₀=2/C=2 显式选取的测度语句包装。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、S10_KVQuantTrig、
   PiEnvelope、LW0MLicBridge、LW5SepComplexity、Local.LW0LeibSeparation、
   LW1PiMeasure、piu1887_piL_uniform_window、piu1901_leibsep_q_kernel_closed。
   对标行：LW1PiMeasure.v lw1m_measure_main（两前提主定理·μ₀=2/C=2 显式选取）
   与 lw1m_measure_main_r2（出窗域零前提形）；LW0LeibSeparation.v
   leibsep_q_kernel（逐 q 实层分离核）与 leibsep_pi_rational_unconditional
   （无条件分离）；piu1901 内核闭合件（eps2 链闭式钉定与窗级伴随定理）。
   构造性注记：零公理零承认零经典；有名语句全 Set 承载（sigT/And/QltT/Id/
   real_lt）；接口位实装按域分段诚实披露——正数域证书取 eps2 链闭式钉定形
   （钉定项含 projT1 包络见证，项级自反而非可计算字面），非正数域取树内
   无条件分离见证；证内 Q 线性不等式段以 lra 承担（辅助步，例外册在册用法，
   于此申报），主定理收尾为既有闭合件合成链非求解器。
   编译配方：coqc -native-compiler no -q -Q〈本件目录〉"" -Q
   ConstructiveWorld_vo ""（COQLIB/ROCQLIB 全字面双 export）。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW5SepComplexity.
Require Import Local.LW0LeibSeparation.
Require Import LW1PiMeasure.
Require Import piu1887_piL_uniform_window.
Require Import piu1901_leibsep_q_kernel_closed.

(* ============================================================ *)
(* §1 闭式接口位实装（lw1m_b_cert_face·全域分段：正数域闭式钉定形）      *)
(* ============================================================ *)

Theorem piu1904_b_cert : lw1m_b_cert_face.
Proof.
  intros a b Hab.
  destruct (Qlt_le_dec 0 ((a / b)%Q)) as [Hpos | Hn].
  - (* 正数域：eps2 链闭式证书（钉定肢项级自反·距离肢实层在卷） *)
    destruct (leibsep_q_kernel_closed ((a / b)%Q) (Qlt_to_QltT 0 ((a / b)%Q) Hpos))
      as [c [Hc0 [Hpin Hdist]]].
    exists c. split.
    + exact Hc0.
    + exact Hdist.
  - (* 非正数域：树内无条件分离（同一结论面逐字同构） *)
    exact (leibsep_pi_rational_unconditional a b Hab).
Qed.

(* ============================================================ *)
(* §2 窗级合成：内核闭式伴随定理 × 统一逃逸窗                            *)
(*    窗级证书 c 项＝2·(eps2 链·(1/8))（逐字取自伴随定理钉定肢）；          *)
(*    窗阶 n0(q) := max N(q) (pie_modulus (c(q)·(1/10)))，等词分支钉定。   *)
(* ============================================================ *)

Definition piu1904_cwin_of (q : Q) (Hq : QltT 0 q) : Q :=
  projT1 (leibsep_q_kernel_closed_window q Hq).

Definition piu1904_Nwin_of (q : Q) (Hq : QltT 0 q) : nat :=
  projT1 (snd (snd (projT2 (leibsep_q_kernel_closed_window q Hq)))).

Definition piu1904_n0_of (q : Q) (Hq : QltT 0 q) : nat :=
  piu1887_n0 (piu1904_Nwin_of q Hq) (piu1904_cwin_of q Hq).

Theorem piu1904_escape_window_closed :
  forall (q : Q) (Hq : QltT 0 q),
    sigT (fun n0 : nat =>
      And (Id n0 (piu1904_n0_of q Hq))
          (QltT (lw0m_e n0) (Qabs ((lw0m_xL n0 - q)%Q)))).
Proof.
  intros q Hq.
  exact (piu1887_piL_escape_window_guarded q (piu1904_cwin_of q Hq)
           (piu1904_Nwin_of q Hq)
           (fst (projT2 (leibsep_q_kernel_closed_window q Hq)))
           (projT2 (snd (snd (projT2 (leibsep_q_kernel_closed_window q Hq)))))).
Qed.

(* ============================================================ *)
(* §3 距离级合流：出窗面于阈值 c(q)/3 成立，经 lw1m_escape_to_dist 得      *)
(*    逐 q 距离率证书（μ₀ 参数化·闭式 c 项驱动）。                        *)
(* ============================================================ *)

Theorem piu1904_dist_closed :
  forall (q : Q) (mu0 : nat) (Hq : QltT 0 q),
    lw1m_dist_face q mu0 ((piu1904_cwin_of q Hq * (1 # 3))%Q).
Proof.
  intros q mu0 Hq.
  remember (piu1904_cwin_of q Hq) as cw eqn:Hcwdef.
  unfold piu1904_cwin_of in Hcwdef.
  pose proof (fst (projT2 (leibsep_q_kernel_closed_window q Hq))) as Hcw0.
  rewrite <- Hcwdef in Hcw0.
  pose proof (QltT_to_Qlt _ _ Hcw0) as HcwQ.
  assert (Hc0 : QltT 0 ((cw * (1 # 3))%Q)) by (apply Qlt_to_QltT; lra).
  assert (Hescface : lw1m_escape_face q ((cw * (1 # 3))%Q)).
  { set (n0 := piu1887_n0 (piu1904_Nwin_of q Hq) ((cw * (1 # 3))%Q)).
    pose proof (piu1887_vanish_ge ((cw * (1 # 3))%Q) n0 Hc0
                  (Nat.le_max_r _ _)) as Hvan.
    pose proof (projT2 (snd (snd (projT2 (leibsep_q_kernel_closed_window q Hq))))
                  n0 (NatLe_lift _ _ (Nat.le_max_l _ _))) as Hwinw0.
    rewrite <- Hcwdef in Hwinw0.
    unfold lw1m_escape_face.
    exists n0. split.
    - apply NatLe_lift. unfold n0, piu1887_n0.
      apply (Nat.le_trans 1
               (pie_modulus ((cw * (1 # 3))%Q * (1 # 10)))
               (Nat.max (piu1904_Nwin_of q Hq)
                  (pie_modulus ((cw * (1 # 3))%Q * (1 # 10))))).
      + unfold pie_modulus. apply le_n_S. apply Nat.le_0_l.
      + apply Nat.le_max_r.
    - assert (HescQ : Qlt ((lw0m_e n0 + 2 * (cw * (1 # 3)))%Q)
                       (Qabs ((lw0m_xL n0 - q)%Q))).
      { pose proof (QltT_to_Qlt _ _ Hvan) as A.
        pose proof (QltT_to_Qlt _ _ Hwinw0) as C.
        lra. }
      apply Qlt_to_QltT. exact HescQ. }
  exact (lw1m_escape_to_dist q ((cw * (1 # 3))%Q) mu0 Hc0 Hescface).
Qed.

(* ============================================================ *)
(* §3b 距离率前提面承载形（显式前提位·诚实接口披露）：逐 q 逐 c₀ 出窗面      *)
(*    经 lw1m_escape_to_dist 包装为 lw1m_dom_face（固定 c₀ 全 q 口径的       *)
(*    供给前提居前提位，非本件无前提主张）。                               *)
(* ============================================================ *)

Theorem piu1904_dom_of_escape :
  (forall (q c0 : Q), QltT 0 c0 -> lw1m_escape_face q c0) ->
  lw1m_dom_face.
Proof.
  intros Hesc Hb mu0 C c0 Hc0 HC q.
  exact (lw1m_escape_to_dist q c0 mu0 Hc0 (Hesc q c0 Hc0)).
Qed.

(* ============================================================ *)
(* §4 终形包装：μ₀=2/C=2 率面（树内零前提闭合形）× 闭式接口位实装 ×        *)
(*    统一窗闭式合成——三面合取，即 π 幂率数值证书闭合的语句承载。          *)
(* ============================================================ *)

Theorem piu1904_mu2_certificate :
  And lw1m_measure_face_r2
      (And lw1m_b_cert_face
           (forall (q : Q) (Hq : QltT 0 q),
              sigT (fun n0 : nat =>
                And (Id n0 (piu1904_n0_of q Hq))
                    (QltT (lw0m_e n0) (Qabs ((lw0m_xL n0 - q)%Q)))))).
Proof.
  split.
  - exact lw1m_measure_main_r2.
  - split.
    + exact piu1904_b_cert.
    + exact piu1904_escape_window_closed.
Qed.

Print Assumptions piu1904_b_cert.
Print Assumptions piu1904_escape_window_closed.
Print Assumptions piu1904_dist_closed.
Print Assumptions piu1904_dom_of_escape.
Print Assumptions piu1904_mu2_certificate.

Separate Extraction piu1904_n0_of piu1904_mu2_certificate.
