(* 五字段指针｜模块：Lw4cPiLicFaceNonempty。使命：lw4c_pi_lic_face（＝
   lic_escape_window lw0m_xL lw4c_pi_win，LW4EPiContrast :72）的无条件非空化——
   由 leibsep_escape_window_at（Lw0LeibEscapeAt：对每一有理数 a/b 给出逃逸阶
   n >= 1 使窗距 lw0m_e n 严格小于点距 |a/b - xL n|）给出逐 q 出闸数据型
   lw4p_pi_gate_supply 的项：出闸精度取量 c0 := (|q/1 - xL n| - lw0m_e n)*(1/4)，
   则 lw4c_pi_win n + 2*c0 < |xL n - q|（窗宽换算 lw4c_pi_win n ＝ lw0m_e n，
   Qabs 对称一步），再经单步定理 lw4p_pi_lic_face_of_gate 得无条件见证。
  依赖：S01_BaseRing（And/sigT）、S02_CauchyComplete（QltT/QltT_to_Qlt/
   Qlt_to_QltT）、LW0MLicBridge（lw0m_e/lw0m_xL）、PiEnvelope（pie_mag）、
   LW4EPiContrast（lw4c_pi_win/lw4c_pi_lic_face）、Lw4cPiLicGate
   （lw4p_pi_gate_supply/lw4p_pi_lic_face_of_gate）、Lw0LeibEscapeAt
   （leibsep_escape_window_at）。
  对标行：Lw4cPiLicGate.v :116/:125（出闸数据型与单步定理）；Lw0LeibEscapeAt.v
   :32（逃逸阶见证源）；LW4EPiContrast.v :30/:72（窗宽与对照面）；LW0MLicBridge.v
   :16/:20（窗距/序列名）；UpReqIrrationalCriterion.v :242（窗型）。
  构造性注记：零公理声明、零承认式（件尾 Print Assumptions 应 Closed）；语句面
   全 Set 层（sigT/And/QltT），证内 Prop（Qlt）仅脚手架、出口位一律 Qlt_to_QltT
   回 Set；c0 由正距离取四分之一真算，非空转。诚实边界：本件不主张 e·π、e+π
   无理性等独立性面；lw4c_pi_lic_face 非空化使对照面两支（e 支/π 支）同时具有
   无条件见证。
  编译配方：coqc -native-compiler no -q -Q "<本件目录>" "" -Q
   "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW4EPiContrast.
Require Import Lw4cPiLicGate.
Require Import Lw0LeibEscapeAt.

Lemma lw4p_q1_abs_pos : QltT 0 (Qabs (1 # 1)%Q).
Proof.
  apply Qlt_to_QltT.
  assert (Habs : Qabs (1 # 1)%Q == (1 # 1)%Q) by reflexivity.
  rewrite Habs. lra.
Qed.

Definition lw4p_pi_gate_supply_witness : lw4p_pi_gate_supply.
Proof.
  intro q.
  destruct (leibsep_escape_window_at q 1 lw4p_q1_abs_pos) as [n [Hn1 Hlt]].
  pose proof (QltT_to_Qlt (lw0m_e n)
               (Qabs ((q / 1 - lw0m_xL n)%Q)) Hlt) as Hlt'.
  assert (Eq1 : (q / 1)%Q == q).
  { unfold Qdiv, Qeq. cbn. lia. }
  rewrite Eq1 in Hlt'.
  exists n.
  exists ((Qabs ((q - lw0m_xL n)%Q) - lw0m_e n) * (1 # 4))%Q.
  split.
  - exact Hn1.
  - split.
    + apply Qlt_to_QltT. lra.
    + assert (Ewin : lw4c_pi_win n == lw0m_e n)
        by (unfold lw4c_pi_win, lw0m_e, pie_mag, Qdiv; ring).
      apply Qlt_to_QltT.
      rewrite (Qabs_Qminus (lw0m_xL n) q).
      rewrite Ewin.
      lra.
Qed.

Theorem lw4c_pi_lic_face_witness : lw4c_pi_lic_face.
Proof.
  exact (lw4p_pi_lic_face_of_gate lw4p_pi_gate_supply_witness).
Qed.

Print Assumptions lw4p_pi_gate_supply_witness.
Print Assumptions lw4c_pi_lic_face_witness.

Separate Extraction lw4p_pi_gate_supply_witness lw4c_pi_lic_face_witness.
