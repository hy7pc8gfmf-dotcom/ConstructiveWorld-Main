(* 五字段指针｜模块：Lw4cPiLicGate。使命：LW4EPiContrast π 侧供件面（lw4c_pi_lic_face
   ＝ lic_escape_window lw0m_xL lw4c_pi_win）的窗型转写装配——把出闸条件
   （窗距 e N 加倍精度 2*c0 严格小于点距 |xL N − q|，leibsep Q 内核外侧支前提形）
   转写为 lic 逃逸窗见证；给出 lic 窗型 bool 分离判定器 lw4p_licdec
   （lw5n_sep_dec/ir2_sep_dec 同构形：negb∘leiblw_Qleb）及其与出闸条件的双桥；
   使用 NsepFindGeneric 通用搜索：预算内存在逃逸阶即机械返回逃逸阶
   （lw4p_escape_by_find 三定理）。依赖：S01_BaseRing（And/NatLe/id_refl）、
   S02_CauchyComplete（QltT/real_lt）、LW0LeibWindow（leiblw_Id/leiblw_Qleb/
   leiblw_Qleb_inv/leiblw_id_eq/leiblw_id_inv）、PiEnvelope（pie_mag）、
   LW0MLicBridge（lw0m_e/lw0m_xL）、LW4EPiContrast（lw4c_pi_win/lw4c_pi_lic_face/
   lw4c_pi_escape）、NsepFindGeneric（nsep_find/nsep_find_hit/nsep_find_ub）、
   LW5SepComplexity（lw5n_Qleb_false_lt 判定器读出面）、UpReqIrrationalCriterion
   （lic_escape_window 窗型）。
   对标行：LW4EPiContrast.v :67/:72/:99（使用目标三件）；UpReqIrrationalCriterion.v
   :242（lic_escape_window 型）；LW0MLicBridge.v :16/:20（窗距/序列名）；
   LW0LeibSeparation.v :53/:220/:298（出闸门/Q 内核外侧支/α 守卫形——前提形逐字
   对齐，本件即其 lic 窗型下游转写）；NsepFindGeneric.v :45/:67（判定器应用面）；
   LW5SepComplexity.v :301（判定器同构源形）。
   构造性注记：语句面全 Set 层（sigT/And/QltT/leiblw_Id），箭头位 (1 <= N)%nat
   前提为 leiblw_natwin_unbounded/lw4c_e_win_lt_pi_win 认证先例形；零承认式、
   零经典逻辑；判定器纯可计算（negb∘leiblw_Qleb）。诚实边界：逃逸窗对任意 q 的
   无条件非空化＝π 对每有理数的正距离分离（π 落于一切自身窗内：余项
   |π − xL n| < 4/(2n+5) < 5/(2n+1) 逐点，故 q＝π 处无逃逸阶），该无条件面系
   LW0LeibSeparation 内侧支（Niven 松量链 G4a-d，语句面冻结、S3-S5 续作）——
   本件不主张该面；升无条件形的机械入口已全预制：供给
   lw4p_pi_gate_supply（逐 q 出闸数据 (N,c0)）即得 lw4c_pi_lic_face
   （lw4p_pi_lic_face_of_gate 单步），零独立性主张。
   编译配方：coqc -native-compiler no -q -Q "<本件目录>" "" -Q
   "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0LeibWindow.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW4EPiContrast.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.
Require Import UpReqIrrationalCriterion.

(* ============================================================ *)
(* §1 窗宽相容性：π 侧窗＝5·pie_mag n＝5/(2n+1)（LW4EPiContrast        *)
(*    A2 分支同款 ring 一步；leibsep 出闸门与 lic 窗同宽的换算底件）   *)
(* ============================================================ *)

Lemma lw4p_win_eq : forall n : nat,
  lw4c_pi_win n == (5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q.
Proof.
  intro n. unfold lw4c_pi_win, lw0m_e, pie_mag, Qdiv. ring.
Qed.

(* ============================================================ *)
(* §2 出闸条件微件：窗距加严前提 ⟹ 逃逸窗逐点不等式                     *)
(*    （Q 层纯算术链：win N ≤ win N + 2·c0 < |xL N − q| ＝ |q − xL N|） *)
(* ============================================================ *)

Lemma lw4p_win_lt_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  QltT (lw4c_pi_win N) (Qabs ((q - lw0m_xL N)%Q)).
Proof.
  intros q N c0 Hc0 Hg.
  pose proof (QltT_to_Qlt (lw4c_pi_win N + 2 * c0)%Q
               (Qabs ((lw0m_xL N - q)%Q)) Hg) as Hg'.
  pose proof (QltT_to_Qlt 0%Q c0 Hc0) as Hlt0.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (lw4c_pi_win N) (lw4c_pi_win N + 2 * c0)%Q
           (Qabs ((q - lw0m_xL N)%Q))).
  - apply (Qle_trans (lw4c_pi_win N) (lw4c_pi_win N + 0)%Q
             (lw4c_pi_win N + 2 * c0)%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (proj2 (Qplus_le_r 0%Q (2 * c0)%Q (lw4c_pi_win N))).
      apply (Qle_trans 0%Q c0%Q (2 * c0)%Q).
      * apply Qlt_le_weak. exact Hlt0.
      * assert (E : (2 * c0)%Q == (c0 + c0)%Q) by ring. rewrite E.
        apply (Qle_trans c0%Q (c0 + 0)%Q (c0 + c0)%Q).
        -- rewrite Qplus_0_r. apply Qle_refl.
        -- apply (Qplus_le_compat c0%Q c0%Q 0%Q c0%Q).
           ++ apply Qle_refl.
           ++ apply Qlt_le_weak. exact Hlt0.
  - rewrite (Qabs_Qminus q (lw0m_xL N)). exact Hg'.
Qed.

(* ============================================================ *)
(* §3 出闸条件 ⟹ π 侧逃逸窗见证（使用目标 lw4c_pi_escape 直承面；        *)
(*    And 形 lic 窗内块转写；门形总供给型＋单步升格定理）                *)
(* ============================================================ *)

Theorem lw4p_escape_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  (1 <= N)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  lw4c_pi_escape q.
Proof.
  intros q N c0 HN Hc0 Hg.
  exists N. exists HN.
  exact (lw4p_win_lt_of_guard q N c0 Hc0 Hg).
Qed.

Theorem lw4p_lic_block_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  (1 <= N)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  sigT (fun n : nat =>
    And ((1 <= n)%nat)
        (QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)))).
Proof.
  intros q N c0 HN Hc0 Hg. exists N. split.
  - exact HN.
  - exact (lw4p_win_lt_of_guard q N c0 Hc0 Hg).
Qed.

(* 门形总供给型：逐 q 出闸数据 (N, c0)。此型的无条件供出的＝π 对每有理数
   的正距离分离（内侧支续作面），本件以型位显式承载缺口（诚实边界）。 *)
Definition lw4p_pi_gate_supply : Set :=
  forall q : Q,
    sigT (fun N : nat =>
      sigT (fun c0 : Q =>
        And ((1 <= N)%nat)
            (And (QltT 0 c0)
                 (QltT (lw4c_pi_win N + 2 * c0)%Q
                       (Qabs ((lw0m_xL N - q)%Q)))))).

Theorem lw4p_pi_lic_face_of_gate : lw4p_pi_gate_supply -> lw4c_pi_lic_face.
Proof.
  intro Hs. intro q.
  destruct (Hs q) as [N [c0 [HN [Hc0 Hg]]]].
  exact (lw4p_lic_block_of_guard q N c0 HN Hc0 Hg).
Qed.

(* ============================================================ *)
(* §4 lic 窗型 bool 分离判定器（lw5n_sep_dec 同构形）与双桥              *)
(* ============================================================ *)

Definition lw4p_licdec (q : Q) (n : nat) : bool :=
  negb (leiblw_Qleb (Qabs ((q - lw0m_xL n)%Q)) (lw4c_pi_win n)).

Lemma lw4p_licdec_true : forall (q : Q) (n : nat),
  lw4p_licdec q n = true ->
  QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)).
Proof.
  intros q n H. unfold lw4p_licdec in H. apply negb_true_iff in H.
  apply Qlt_to_QltT. exact (lw5n_Qleb_false_lt _ _ H).
Qed.

Lemma lw4p_licdec_of_escape : forall (q : Q) (n : nat),
  QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)) ->
  lw4p_licdec q n = true.
Proof.
  intros q n H. pose proof (QltT_to_Qlt _ _ H) as Hlt.
  unfold lw4p_licdec.
  destruct (leiblw_Qleb (Qabs ((q - lw0m_xL n)%Q)) (lw4c_pi_win n)) eqn:E;
    simpl.
  - exfalso. pose proof (leiblw_Qleb_inv _ _ E) as Hle.
    exact (Qlt_irrefl (lw4c_pi_win n) (Qlt_le_trans _ _ _ Hlt Hle)).
  - reflexivity.
Qed.

Lemma lw4p_licdec_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  (1 <= N)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  lw4p_licdec q N = true.
Proof.
  intros q N c0 HN Hc0 Hg. apply lw4p_licdec_of_escape.
  exact (lw4p_win_lt_of_guard q N c0 Hc0 Hg).
Qed.

(* ============================================================ *)
(* §5 通用判定器应用面：预算搜索即逃逸阶机械供给                          *)
(* ============================================================ *)

Definition lw4p_escape_by_find (q : Q) (b : nat) : nat :=
  nsep_find lw4p_licdec q 1 b.

Lemma lw4p_find_ge1 : forall (q : Q) (b n : nat), (1 <= n)%nat ->
  (1 <= nsep_find lw4p_licdec q n b)%nat.
Proof.
  intros q b. induction b as [|b IH]; intros n Hn; simpl.
  - exact Hn.
  - destruct (lw4p_licdec q n).
    + exact Hn.
    + apply IH. lia.
Qed.

Lemma lw4p_find_ub : forall (q : Q) (b : nat),
  (lw4p_escape_by_find q b <= 1 + b)%nat.
Proof.
  intros q b. unfold lw4p_escape_by_find.
  pose proof (nsep_find_ub lw4p_licdec q b 1) as H. lia.
Qed.

Lemma lw4p_find_escape : forall (q : Q) (b n0 : nat),
  (1 <= n0)%nat -> (n0 <= 1 + b)%nat ->
  QltT (lw4c_pi_win n0) (Qabs ((q - lw0m_xL n0)%Q)) ->
  QltT (lw4c_pi_win (lw4p_escape_by_find q b))
       (Qabs ((q - lw0m_xL (lw4p_escape_by_find q b))%Q)).
Proof.
  intros q b n0 H1 H2 Hesc. unfold lw4p_escape_by_find.
  assert (Hdec : leiblw_Id (lw4p_licdec q n0) true).
  { rewrite (lw4p_licdec_of_escape q n0 Hesc). apply leiblw_id_intro. }
  destruct (nsep_find_hit lw4p_licdec q b 1 n0 H1 H2 Hdec) as [Hh _].
  apply leiblw_id_inv in Hh.
  apply lw4p_licdec_true. exact Hh.
Qed.

(* 出闸条件 ⟹ 预算搜索命中逃逸阶（出闸数据→可计算见证的全链闭合） *)
Theorem lw4p_find_escape_of_guard : forall (q : Q) (b N : nat) (c0 : Q),
  (1 <= N)%nat -> (N <= 1 + b)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  QltT (lw4c_pi_win (lw4p_escape_by_find q b))
       (Qabs ((q - lw0m_xL (lw4p_escape_by_find q b))%Q)).
Proof.
  intros q b N c0 H1 H2 Hc0 Hg.
  exact (lw4p_find_escape q b N H1 H2
          (lw4p_win_lt_of_guard q N c0 Hc0 Hg)).
Qed.

(* ============================================================ *)
(* §6 数值抽查（可计算面闭项；q＝0 在 1 阶即出窗：8/3 > 5/3）            *)
(* ============================================================ *)

Lemma lw4p_licdec_tbl_zero : leiblw_Id (lw4p_licdec 0%Q 1) true.
Proof. apply leiblw_id_eq. reflexivity. Qed.

Eval vm_compute in
  (lw4p_escape_by_find (22 # 7)%Q 200,
   lw4p_escape_by_find (3 # 1)%Q 200,
   lw4p_escape_by_find 0%Q 3).

(* ============================================================ *)
(* §7 提取＋假设审计（红线④）                                          *)
(* ============================================================ *)

Separate Extraction lw4p_licdec lw4p_escape_by_find lw4p_win_eq
  lw4p_escape_of_guard lw4p_find_escape lw4p_pi_lic_face_of_gate.

Print Assumptions lw4p_escape_of_guard.
Print Assumptions lw4p_find_escape.
Print Assumptions lw4p_pi_lic_face_of_gate.
Print Assumptions lw4p_licdec_true.
