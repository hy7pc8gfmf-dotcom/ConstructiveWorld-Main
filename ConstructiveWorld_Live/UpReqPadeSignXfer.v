(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 九批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   psx_beta_bridge（原 L119，2 句玩具证；裸 reflexivity→Qeq_refl 显式见证项 1 刀）*)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeSignXfer.v *)
(* *)
(* 目的： pbp_sign_transfer 的实例化传送件。 *)
(* 主件： psx_sign_instantiated 与 psx_sign_pair / psx_beta_bridge 传送链。 *)
(* 依赖： S02_CauchyComplete、S03_QExp、UpReqPadeBetaPos、UpReqPadeTailPos。 *)
(* 备注： 实例化件：符号对经 β 桥传送；系数积正性为构造核。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeSignXfer.v —— AA2·A6：pbp_sign_transfer     *)
(* （；A 档消融工程第一批第二单，后台独立作业）           *)
(* ============================================================ *)
(* 使命：把 C-T1b 的 pbp_sign_transfer（lead == β_m·posf ⟹ 正，  *)
(*   接口参数 posf 显式留白）用 C-T1a 库内实件填上，产出「余项    *)
(*   首项符号 = (−1)^n·正」的落地使用件（偶 n 正/奇 n 负对偶      *)
(*   显式）。                                                    *)
(*                                                             *)
(* 纪律：禁改 BetaPos/TailPos 本体一行——只 Require 使用。        *)
(*                                                             *)
(* 落地面（语句形以两源件实形适配）：                             *)
(*   β_m 双库同式：pbp_beta = ptp_beta = n!(n+m)!/(2n+m+1)!       *)
(*     （双透明 Definition 逐字同构，psx_beta_bridge 一行承桥）。 *)
(*   首项系数（TailPos 定值面对表）：coef n = ptp_beta n 0/(2n)!  *)
(*     （n=1 得 1/12，n=2 得 1/720，psx_coef_vals 直取定值件）。  *)
(*   带号首项系数：psx_signed n = psx_sign n · coef n，           *)
(*     psx_sign 交替 ±1 = (−1)^n。                               *)
(*   主件 psx_sign_instantiated（pbp_sign_transfer 接口实例化）： *)
(*     lead == psx_sign n · coef n ⟹ 0 < psx_sign n · lead        *)
(*   即 (−1)^n·(带号首项) 恒正——偶支=传送件直接实例化，           *)
(*   奇支=对偶面（去号后同一传送件提供实参）。                        *)
(*   独立正性件 psx_coef_pos：TailPos 侧 ptp_beta_pos 全称面      *)
(*     显式应用首系数（与传送面交叉印证系数幅正值）。                 *)
(*                                                             *)




(*                                                             *)
(* 红线自审：语句面全 Set（QltT/Qeq/sigT 均既有 Set 承载面）；    *)
(*   无新增 Prop 判断面（Qeq 前提沿 pbp_sign_transfer 既有形）；  *)
(*   无假设件；无公理/承认件/弃证面。                             *)
(* ============================================================ *)

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeBetaPos.
Require Import UpReqPadeTailPos.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

(* ===== S1 定义面 ===== *)

(* (−1)^n 符号交替（Fixpoint 双步回绕：1,−1,1,−1,…，Set 层） *)
Fixpoint psx_sign (n : nat) : Q :=
  match n with
  | Datatypes.O => 1%Q
  | Datatypes.S Datatypes.O => (-1)%Q
  | Datatypes.S (Datatypes.S n') => psx_sign n'
  end.

(* 正因子部：1/(2n)!——pbp_sign_transfer 的 posf 槽实例 *)
Definition psx_posf (n : nat) : Q := 1%Q / q_fact (2 * n).

(* 首项系数（TailPos 定值面实形）：ptp_beta n 0 / (2n)! *)
Definition psx_coef (n : nat) : Q := ptp_beta n 0 / q_fact (2 * n).

(* 带号首项系数：(−1)^n · coef n——偶 n 正/奇 n 负 *)
Definition psx_signed (n : nat) : Q := psx_sign n * psx_coef n.

(* ===== S2 符号小引擎 ===== *)

(* 奇偶配对归纳（双步回绕一次性给全 ±1 面） *)
Lemma psx_sign_pair : forall n : nat,
  psx_sign (2 * n) == 1%Q /\ psx_sign (2 * n + 1) == (-1)%Q.
Proof.
  induction n as [| n IH].
  - split; reflexivity.
  - destruct IH as [IH1 IH2]. split.
    + replace ((2 * Datatypes.S n)%nat)
        with (Datatypes.S (Datatypes.S (2 * n))) by lia.
      exact IH1.
    + replace ((2 * Datatypes.S n + 1)%nat)
        with (Datatypes.S (Datatypes.S (2 * n + 1))) by lia.
      exact IH2.
Qed.

Lemma psx_sign_double : forall k : nat, psx_sign (2 * k) == 1%Q.
Proof. intro k. destruct (psx_sign_pair k) as [Hp _]. exact Hp. Qed.

Lemma psx_sign_odd : forall k : nat, psx_sign (2 * k + 1) == (-1)%Q.
Proof. intro k. destruct (psx_sign_pair k) as [_ Ho]. exact Ho. Qed.

(* 符号平方归一（主件去号完成用） *)
Lemma psx_sign_sq : forall n : nat, psx_sign n * psx_sign n == 1%Q.
Proof.
  intro n.
  assert (H : forall m : nat,
            psx_sign m * psx_sign m == 1%Q /\
            psx_sign (Datatypes.S m) * psx_sign (Datatypes.S m) == 1%Q).
  { induction m as [| m IH].
    - split; simpl; ring.
    - destruct IH as [IH1 IH2]. split.
      + exact IH2.
      + simpl. exact IH1. }
  apply H.
Qed.

(* 正性引擎：posf 恒正（1/(2n)! 严格正，Qlt 面组装） *)
Lemma psx_posf_pos : forall n : nat, QltT 0 (psx_posf n).
Proof.
  intro n. apply Qlt_to_QltT. unfold psx_posf, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (H01 : Qlt 0%Q 1%Q) by (unfold Qlt; cbn [Qnum Qden]; lia).
    exact H01.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* 双库桥：pbp_beta 与 ptp_beta 闭式逐字同构（透明 Definition 转换面） *)
Lemma psx_beta_bridge : forall n m : nat, ptp_beta n m == pbp_beta n m.
Proof. intros n m. exact (Qeq_refl (ptp_beta n m)). Qed.

(* 系数积形：coef n = ptp_beta n 0 · posf n（喂传送接口的积形） *)
Lemma psx_coef_prod : forall n : nat, psx_coef n == ptp_beta n 0 * psx_posf n.
Proof.
  intro n. unfold psx_coef, psx_posf, Qdiv.
  rewrite Qmult_1_l. reflexivity.
Qed.

(* ===== S3 主件：符号传送落地（pbp_sign_transfer 接口实例化） ===== *)

Theorem psx_sign_instantiated : forall (lead : Q) (n : nat),
  lead == psx_sign n * psx_coef n ->
  QltT 0 (psx_sign n * lead).
Proof.
  intros lead n Heq.
  apply (pbp_sign_transfer (psx_sign n * lead) (psx_posf n) n 0).
  - (* 去号完成：(−1)^n·lead = (−1)^n·((−1)^n·coef) = coef = β·posf *)
    rewrite Heq.
    rewrite Qmult_assoc.
    rewrite psx_sign_sq.
    rewrite Qmult_1_l.
    rewrite psx_coef_prod.
    rewrite psx_beta_bridge.
    reflexivity.
  - apply psx_posf_pos.
Qed.

(* TailPos 侧独立正性件：ptp_beta_pos 全称面显式应用首系数 *)
Corollary psx_coef_pos : forall n : nat, QltT 0 (psx_coef n).
Proof.
  intro n. apply Qlt_to_QltT. unfold psx_coef, Qdiv.
  apply Qmult_lt_0_compat.
  - apply QltT_to_Qlt. apply ptp_beta_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* 定值对表（TailPos 定值件直取）：coef 1 = 1/12，coef 2 = 1/720 *)
Lemma psx_coef_vals :
  psx_coef 1%nat == (1#12)%Q /\ psx_coef 2%nat == (1#720)%Q.
Proof. split; [exact ptp_beta_n1_first | exact ptp_beta_n2_first]. Qed.

(* ===== S4 对偶显式：偶 n 首系数正 / 奇 n 首系数负 ===== *)

(* 偶支：带号首项系数严格正（(−1)^(2k) = +1 直实例化；
   QltT 无 Qeq-Proper 实例——换号一律走 pbp_qlt0_eq_r 传桥，
   rewrite 只在 Qeq 目标内进行） *)
Corollary psx_even_pos : forall k : nat, QltT 0 (psx_signed (2 * k)).
Proof.
  intro k.
  apply Qlt_to_QltT.
  apply (pbp_qlt0_eq_r
           (psx_sign (2 * k) * psx_signed (2 * k)) (psx_signed (2 * k))).
  - unfold psx_signed. rewrite psx_sign_double. ring.
  - apply QltT_to_Qlt.
    apply (psx_sign_instantiated (psx_signed (2 * k)) (2 * k)).
    unfold psx_signed. reflexivity.
Qed.

(* 奇支对偶：带号首项系数负（其相反数去号后严格正）——
   a = psx_sign·psx_signed（去号形）与 b = −psx_signed 恒等；
   传送件实例取 lead := psx_signed（奇号下其前提为真形） *)
Corollary psx_odd_neg : forall k : nat, QltT 0 (- psx_signed (2 * k + 1)).
Proof.
  intro k.
  apply Qlt_to_QltT.
  apply (pbp_qlt0_eq_r
           (psx_sign (2 * k + 1) * psx_signed (2 * k + 1))
           (- psx_signed (2 * k + 1))).
  - unfold psx_signed. rewrite psx_sign_odd. ring.
  - apply QltT_to_Qlt.
    apply (psx_sign_instantiated (psx_signed (2 * k + 1)) (2 * k + 1)).
    unfold psx_signed. reflexivity.
Qed.


Print Assumptions psx_sign_instantiated.
Print Assumptions psx_coef_pos.
Print Assumptions psx_even_pos.
Print Assumptions psx_odd_neg.
Print Assumptions psx_coef_vals.

From Stdlib Require Import Extraction.
Separate Extraction psx_sign_instantiated psx_signed psx_coef psx_posf
  psx_sign psx_coef_pos psx_coef_vals.
