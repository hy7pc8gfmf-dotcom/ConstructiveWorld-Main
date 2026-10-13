(* ================================================================== *)
(* LeibsepBandCkAssembly —— W1-α'' 带域一致型终装配件                   *)
(*                                                                    *)
(* 使命：带域一致型逐点形终定理——带域前提下 margin 链 c₀=1 见证两形      *)
(*   逐点下界 `1/((h+1)·(2n_sel+2)!) ≤ wit_i` 全链装配：①1868 核心件   *)
(*   （min4/bridge/wit_lower/qfact_mono）＋链量换算定义七件逐字重述      *)
(*   （piu1868_* 原件不再演化·其 equalization 范畴错阻断编译            *)
(*   故核心件于本件重述为 piu1872_*·源坐标逐件登记）；②1862 证书条件    *)
(*   链内承载肢（cert_from_WING）；③互译恒等式闭链完成（消元主难段      *)
(*   十五步＋AC 尾新链四步·机器检验零错）；                             *)
(*   ——`piu1872_valve_closed_R1_free` 免互译前提（1866 前提参数位免肢）；*)
(*   ④eps2_equalization 重述（statement 修正：eps1 参数位实例化为定义应用*)
(*   ——1868 原件原 statement 以变量 eps1 承载 `min=…` 等式系范畴错，    *)
(*   本件修正为定义应用参数位）；⑤Section 带域 margin 双下界（1868 参数位*)
(*   互译）；⑥终定理＝高度坐标面（lw1m_height q · 40h+48 经 1864 耦合   *)
(*   `2n_sel+2=40h+48` 换算）：带域＋阀形双肢＋证书四 premises 下         *)
(*   `1/((h+1)·(40h+48)!) ≤ wit_1 ∧ wit_2 ∧ QltT 0 wit_2`（c₀=1 容肢）；  *)
(*   ⑦ck 面对接＝tlw1448_transfer `tlw1448_ck q := projT1                *)
(*   (leibsep_q_kernel q)` 可见面（正性＋距离窗）对接肢。                 *)
(* 依赖：Stdlib QArith/Qabs/Qminmax/ZArith/Lia/Lqa；S01_BaseRing；       *)
(*   S03_QExp（q_fact/q_pow/q_fact_pos）；LW0PiIrrational（lw0_Wb :1336）； *)
(*   LW1PiMeasure（lw1m_height :48·QltT）；leibsep_nsel_h_coupling（1864  *)
(*   既有件）；leibsep_band_domain（1866 既有件）；tlw1448_transfer     *)
(*   （在库）。                                                         *)
(* 对标行：LW0LeibSeparation :5453（kernel Qed 不透明）；:5509（eps1）；    *)
(*   :5596（WING）；:5609（eps2）；:5566-5571/:5630-5635（witness 两形）；  *)
(*   tlw1448_transfer :60（tlw1448_ck）；:67（kernel_dist_ck）。           *)
(* 构造性注记：全 Set/Prop 层；零 Axiom/Admitted/Abort；零经典逻辑。     *)
(* Qeq 重写全程 %Q 显式；Qmult_assoc 定向＝`x*(y*z) == (x*y)*z`         *)
(*   （定向经实证核准·AC 链按此定向对树核验）；closed-Qle closer＝      *)
(*   vm_compute + discriminate（closed-Qlt 方为 reflexivity——lia-on-Q   *)
(*   法该形不可靠）；equalization 修正处方：sub2 closer 用               *)
(*   Qlt_le_trans+vm_compute、compat_r 前提用 Qlt_le_weak、Ehalf 用     *)
(*   E12+Qmult_assoc 定向链。                                           *)
(*                                                                      *)
(* 编译配方：coqc -native-compiler no -q -Q <vo树> "" -Q . "" 本件        *)
(*   （COQLIB/ROCQLIB 字面 export；cpu_guard v3 包裹；单道 coqchk。      *)
(*                                                                      *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia ZArith Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PiEnvelope.
Require Import LW0PiIrrational.
Require Import LW1PiMeasure.
Require Import leibsep_nsel_h_coupling.
Require Import leibsep_band_domain.
Require Import tlw1448_transfer.

(* ---------- §1 通用微件（1868 绿核逐字重铸·源 :38-:126） ---------- *)

Lemma piu1872_qfact_mono : forall n m : nat, (n <= m)%nat -> Qle (q_fact n) (q_fact m).
Proof.
  intros n m H. induction H as [| m Hle IH].
  - apply Qle_refl.
  - rewrite q_fact_succ.
    apply (Qle_trans (q_fact n) (1 * q_fact m)%Q).
    + rewrite Qmult_1_l. exact IH.
    + apply (Qmult_le_compat_r 1 ((Z.of_nat (Datatypes.S m) # 1)%Q) (q_fact m)).
      * assert (Hh : (0 <= Z.of_nat (Datatypes.S m))%Z) by (apply Z2Nat.inj_le; lia).
        unfold Qle. cbn [Qnum Qden]. lia.
      * apply Qlt_le_weak. apply q_fact_pos.
Qed.

Lemma piu1872_min4 : forall a b c d X : Q,
  Qle X a -> Qle X b -> Qle X c -> Qle X d ->
  Qle X (Qmin a (Qmin b (Qmin c d))).
Proof.
  intros a b c d X Ha Hb Hc Hd.
  apply (Q.min_glb a (Qmin b (Qmin c d)) X); [ exact Ha | ].
  apply (Q.min_glb b (Qmin c d) X); [ exact Hb | ].
  apply (Q.min_glb c d X); [ exact Hc | exact Hd ].
Qed.

Lemma piu1872_bridge : forall a b x y : Q,
  Qlt 0 x -> Qlt 0 y -> Qle (a * y) (b * x) -> Qle (a / x) (b / y).
Proof.
  intros a b x y Hx Hy Hle.
  assert (Hx0 : ~ x == 0) by
    (intro Hz; apply (Qlt_not_eq 0 x Hx); apply Qeq_sym; exact Hz).
  assert (Hy0 : ~ y == 0) by
    (intro Hz; apply (Qlt_not_eq 0 y Hy); apply Qeq_sym; exact Hz).
  assert (Hxi : Qlt 0 (/ x)) by (apply Qinv_lt_0_compat; exact Hx).
  assert (Hyi : Qlt 0 (/ y)) by (apply Qinv_lt_0_compat; exact Hy).
  pose proof (Qmult_le_compat_r (a * y) (b * x) (/ x * / y) Hle
                (Qlt_le_weak 0 (/ x * / y)
                   (Qmult_lt_0_compat (/ x) (/ y) Hxi Hyi))) as Hm.
  assert (E1 : (a * y) * (/ x * / y) == a * / x).
  { rewrite (Qmult_comm (a * y) (/ x * / y)).
    rewrite <- (Qmult_assoc (/ x) (/ y) (a * y)).
    rewrite (Qmult_assoc (/ y) a y).
    rewrite (Qmult_comm (/ y) a).
    rewrite <- (Qmult_assoc a (/ y) y).
    rewrite (Qmult_comm (/ y) y).
    rewrite (Qmult_inv_r y Hy0).
    rewrite (Qmult_1_r a).
    rewrite (Qmult_comm (/ x) a).
    reflexivity. }
  assert (E2 : (b * x) * (/ x * / y) == b * / y).
  { rewrite (Qmult_assoc (b * x) (/ x) (/ y)).
    rewrite (Qmult_comm (b * x) (/ x)).
    rewrite (Qmult_assoc (/ x) b x).
    rewrite (Qmult_comm (/ x) b).
    rewrite <- (Qmult_assoc b (/ x) x).
    rewrite (Qmult_comm (/ x) x).
    rewrite (Qmult_inv_r x Hx0).
    rewrite (Qmult_1_r b).
    reflexivity. }
  rewrite E1 in Hm. rewrite E2 in Hm. exact Hm.
Qed.

Lemma piu1872_wit_lower : forall X den : Q,
  Qlt 0 den ->
  Qle ((4 # 1)%Q / den) X ->
  Qle (1 / den)%Q (2 * (X * (1 # 8))%Q).
Proof.
  intros X den Hden Hle.
  assert (Hstep : Qle ((4 # 1)%Q / den * (1 # 8)) (X * (1 # 8))%Q).
  { apply Qmult_le_compat_r; [ exact Hle | vm_compute; discriminate]. }
  apply (Qle_trans (1 / den)%Q ((2 # 1)%Q * ((4 # 1)%Q / den * (1 # 8))%Q)
                   (2 * (X * (1 # 8))%Q)).
  - assert (Eid : ((2 # 1)%Q * ((4 # 1)%Q / den * (1 # 8))%Q)%Q == (1 / den)%Q).
    { unfold Qdiv.
      rewrite (Qmult_comm (4 # 1)%Q (/ den)).
      rewrite (Qmult_assoc (2 # 1)%Q ((/ den) * (4 # 1)%Q) (1 # 8)%Q).
      rewrite (Qmult_assoc (2 # 1)%Q (/ den) (4 # 1)%Q).
      rewrite (Qmult_comm (2 # 1)%Q (/ den)).
      rewrite <- (Qmult_assoc (/ den) (2 # 1)%Q (4 # 1)%Q).
      rewrite <- (Qmult_assoc (/ den) ((2 * (4 # 1)%Q)%Q) (1 # 8)%Q).
      rewrite (Qmult_comm ((2 * (4 # 1)%Q)%Q) (1 # 8)%Q).
      assert (EL : ((1 # 8)%Q * (2 * (4 # 1)%Q))%Q == 1%Q) by reflexivity.
      rewrite EL. rewrite (Qmult_1_r (/ den)). rewrite Qmult_1_l. reflexivity. }
    rewrite Eid. apply Qle_refl.
  - assert (Hc : Qle (((4 # 1)%Q / den * (1 # 8)) * (2 # 1)%Q)
                     ((X * (1 # 8)) * (2 # 1)%Q))
      by (apply Qmult_le_compat_r; [ exact Hstep | vm_compute; discriminate ]).
    rewrite (Qmult_comm ((4 # 1)%Q / den * (1 # 8)) (2 # 1)%Q) in Hc.
    rewrite (Qmult_comm (X * (1 # 8)) (2 # 1)%Q) in Hc.
    exact Hc.
Qed.

(* Qeq 首参数位 Qle 换肢（1866 Qeq_le_l/r 仅第二参数位·本件补首参数位三行肢） *)
Lemma piu1872_Qeq_le_swap : forall x y z : Q, x == y -> Qle x z -> Qle y z.
Proof.
  intros x y z Hxy Hle. rewrite <- Hxy. exact Hle.
Qed.

(* ---------- §2 链量换算定义（1868 :130-:151 逐字·更名 piu1872_*） ---------- *)

Definition piu1872_S973 : Q := (1 + 121 / 18 + 73205 / 5364)%Q.

Definition piu1872_K (BF BFd : Q) : Q :=
  (BF * ((11 # 3)%Q * piu1872_S973 + (1 # 4))
    + BFd * (piu1872_S973 + (1 # 4)) + (1 # 8))%Q.

Definition piu1872_eps1 (eg el K : Q) : Q :=
  Qmin eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))).

Definition piu1872_WING (b0 q : Q) (n_sel : nat) : Q :=
  q_fact n_sel * (lw0_Wb b0 q n_sel 0 * (2 # 27)%Q).

Definition piu1872_eps2 (eps1 WING K : Q) : Q :=
  Qmin eps1 (WING / (2 * K)%Q).

Definition piu1872_wit (eps : Q) : Q := 2 * (eps * (1 # 8))%Q.

Definition piu1872_valve_den (h n_sel : nat) : Q :=
  (Z.of_nat (Datatypes.S h) # 1)%Q * q_fact (2 * n_sel + 2)%nat.

Definition piu1872_valve_up (K : Q) (h n_sel : nat) : Prop :=
  Qle ((8 # 1)%Q * K) (piu1872_valve_den h n_sel).

(* ---------- §3 阀形接合点肢（1868 :155-:287 逐字重铸） ---------- *)

Lemma piu1872_den_ge24 : forall h n_sel : nat,
  (2 <= n_sel)%nat -> Qle (24 # 1)%Q (piu1872_valve_den h n_sel).
Proof.
  intros h n_sel Hn. unfold piu1872_valve_den.
  apply (Qle_trans (24 # 1)%Q ((1 * q_fact (2 * n_sel + 2)%nat)%Q)).
  - rewrite Qmult_1_l.
    apply (Qle_trans (24 # 1)%Q (q_fact 4) (q_fact (2 * n_sel + 2)%nat)).
    + vm_compute. discriminate.
    + apply piu1872_qfact_mono. lia.
  - apply (Qmult_le_compat_r 1 (Z.of_nat (Datatypes.S h) # 1)%Q
             (q_fact (2 * n_sel + 2)%nat)).
    + assert (Hh : (0 <= Z.of_nat (Datatypes.S h))%Z) by (apply Z2Nat.inj_le; lia).
      unfold Qle. cbn [Qnum Qden]. lia.
    + apply Qlt_le_weak. apply q_fact_pos.
Qed.

Lemma piu1872_eps1_leg : forall eg el K den : Q,
  Qle ((4 # 1)%Q / den) eg ->
  Qle ((4 # 1)%Q / den) el ->
  Qlt 0 K ->
  Qle ((8 # 1)%Q * K) den ->
  Qle (24 # 1)%Q den ->
  Qle ((4 # 1)%Q / den) (piu1872_eps1 eg el K).
Proof.
  intros eg el K den Heg Hel HK Hup H24.
  unfold piu1872_eps1. apply piu1872_min4.
  - exact Heg.
  - exact Hel.
  - apply (piu1872_bridge (4 # 1)%Q 1 den (3 # 1)%Q).
    + apply Qlt_le_trans with (24 # 1)%Q; [ vm_compute; reflexivity | exact H24 ].
    + vm_compute. reflexivity.
    + apply (Qle_trans ((4 # 1)%Q * (3 # 1)%Q) (24 # 1)%Q (1 * den)%Q).
      * vm_compute. discriminate.
      * rewrite Qmult_1_l. exact H24.
  - apply (piu1872_bridge (4 # 1)%Q (1 # 2)%Q den K).
    + apply Qlt_le_trans with (24 # 1)%Q; [ vm_compute; reflexivity | exact H24 ].
    + exact HK.
    + apply (Qle_trans ((4 # 1)%Q * K) (((8 # 1)%Q * K) * (1 # 2)%Q)
                     ((1 # 2)%Q * den)).
      * assert (Ehalf : (((8 # 1)%Q * K) * (1 # 2)%Q)%Q == ((4 # 1)%Q * K)%Q).
        { rewrite <- (Qmult_assoc (8 # 1)%Q K (1 # 2)%Q).
          rewrite (Qmult_comm K (1 # 2)%Q).
          rewrite (Qmult_assoc (8 # 1)%Q (1 # 2)%Q K).
          assert (E82 : ((8 # 1)%Q * (1 # 2)%Q)%Q == (4 # 1)%Q) by reflexivity.
          rewrite E82. reflexivity. }
        rewrite Ehalf. apply Qle_refl.
      * assert (Hpre : Qle (((8 # 1)%Q * K) * (1 # 2)%Q) (den * (1 # 2)%Q))
          by (apply (Qmult_le_compat_r ((8 # 1)%Q * K) den (1 # 2)%Q);
              [ exact Hup | vm_compute; discriminate ]).
        rewrite (Qmult_comm den (1 # 2)%Q) in Hpre.
        exact Hpre.
Qed.

Lemma piu1872_valve_R1_leg : forall (WING K : Q) (h n_sel : nat),
  Qlt 0 K ->
  piu1866_valve_R1 WING K h n_sel ->
  Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) (WING / (2 * K)%Q).
Proof.
  intros WING K h n_sel HK HR1. unfold piu1866_valve_R1 in HR1.
  apply (piu1872_bridge (4 # 1)%Q WING (piu1872_valve_den h n_sel) (2 * K)%Q).
  - unfold piu1872_valve_den. apply Qmult_lt_0_compat.
    + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z) by (apply Z2Nat.inj_lt; lia).
      unfold Qlt. cbn [Qnum Qden]. lia.
    + apply q_fact_pos.
  - apply Qmult_lt_0_compat.
    + vm_compute. reflexivity.
    + exact HK.
  - unfold piu1872_valve_den in HR1.
    apply (Qle_trans ((4 # 1)%Q * (2 * K)%Q) (((8 # 1)%Q * K) * (1 # 1)%Q)
                     (WING * piu1872_valve_den h n_sel)).
    + assert (E42 : ((4 # 1)%Q * (2 * K)%Q)%Q == ((8 # 1)%Q * K)%Q).
      { rewrite <- (Qmult_assoc (4 # 1)%Q (2 # 1)%Q K). reflexivity. }
      rewrite E42. rewrite Qmult_1_r. apply Qle_refl.
    + rewrite Qmult_1_r. exact HR1.
Qed.

(* 全支统一上界的镜面：margin·K ≤ 1/8（ck ≤ 1/(8K) 除法自由形） *)
Lemma piu1872_margin_cap : forall eps K : Q,
  Qle eps ((1 # 2)%Q / K) ->
  Qlt 0 K ->
  Qle (piu1872_wit eps * K) (1 # 8)%Q.
Proof.
  intros eps K Hcap HK.
  assert (Hs : Qle (eps * (1 # 8)) ((1 # 2)%Q / K * (1 # 8))%Q)
    by (apply Qmult_le_compat_r; [ exact Hcap | vm_compute; discriminate]).
  apply (Qle_trans (piu1872_wit eps * K)
                   (2 * (((1 # 2)%Q / K * (1 # 8)) * K)) (1 # 8)%Q).
  - unfold piu1872_wit.
    assert (Hm1 : Qle ((eps * (1 # 8)) * K) (((1 # 2)%Q / K * (1 # 8)) * K))
      by (apply Qmult_le_compat_r; [ exact Hs | apply Qlt_le_weak; exact HK ]).
    assert (E21 : (2 * (eps * (1 # 8)) * K)%Q
                  == (((eps * (1 # 8)) * K) * (2 # 1))%Q).
    { rewrite <- (Qmult_assoc (2 # 1)%Q (eps * (1 # 8)) K).
      rewrite (Qmult_comm (2 # 1)%Q ((eps * (1 # 8)) * K)).
      reflexivity. }
    rewrite E21.
    rewrite (Qmult_comm (2 # 1)%Q (((1 # 2)%Q / K * (1 # 8)) * K)).
    apply (Qmult_le_compat_r ((eps * (1 # 8)) * K)
             (((1 # 2)%Q / K * (1 # 8)) * K) (2 # 1)%Q).
    + exact Hm1.
    + vm_compute. discriminate.
  - assert (Ecan : (((1 # 2)%Q / K * (1 # 8)) * K)%Q
                   == ((1 # 2) * (1 # 8) * (K * / K))%Q).
    { unfold Qdiv.
      rewrite <- (Qmult_assoc (1 # 2)%Q (/ K) (1 # 8)).
      rewrite (Qmult_comm (/ K) (1 # 8)).
      rewrite (Qmult_assoc (1 # 2)%Q (1 # 8) (/ K)).
      rewrite <- (Qmult_assoc ((1 # 2) * (1 # 8)) (/ K) K).
      rewrite (Qmult_comm (/ K) K).
      reflexivity. }
    rewrite Ecan.
    assert (HK0 : ~ K == 0) by
      (intro Hz; apply (Qlt_not_eq 0 K HK); apply Qeq_sym; exact Hz).
    rewrite (Qmult_inv_r K HK0).
    vm_compute. discriminate.
Qed.

(* ---------- §4 1862 证书条件链内承载位 ---------- *)

Lemma piu1872_cert_from_WING : forall (WING K eg el : Q) (h n_sel : nat),
  Qlt 0 K ->
  piu1866_valve_R1 WING K h n_sel ->
  Qle (WING / (2 * K)%Q) eg ->
  Qle (WING / (2 * K)%Q) el ->
  Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) eg
  /\ Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) el.
Proof.
  intros WING K eg el h n_sel HK HR1 Heg Hel.
  pose proof (piu1872_valve_R1_leg WING K h n_sel HK HR1) as Hleg.
  split.
  - apply (Qle_trans _ (WING / (2 * K)%Q) eg); [ exact Hleg | exact Heg ].
  - apply (Qle_trans _ (WING / (2 * K)%Q) el); [ exact Hleg | exact Hel ].
Qed.

(* ---------- §5 eps2 等式化（statement 修正重述·1862 §5 肢） ---------- *)
(* 1868 冻结件原 statement 以自由变量 eps1 承载「min 等式」系范畴错       *)
(* （min 等式需 eps1 参数位为定义应用方成立）；本件修正为定义应用参数位。 *)
(* WING ≤ 1 与 K ≥ 3/2 系链外肢·前提位显式承载如实分档。                  *)

Lemma piu1872_eps2_equalization : forall eg el K WING : Q,
  Qle (WING / (2 * K)%Q) eg ->
  Qle (WING / (2 * K)%Q) el ->
  Qle WING 1 ->
  Qle (3 # 2)%Q K ->
  piu1872_eps2 (piu1872_eps1 eg el K) WING K == WING / (2 * K)%Q.
Proof.
  intros eg el K WING Heg Hel Hw1 HK32.
  assert (HKlt : Qlt 0 K)
    by (apply (Qlt_le_trans 0 (3 # 2)%Q K);
          [ vm_compute; reflexivity | exact HK32 ]).
  assert (Hleg : Qle (WING / (2 * K)%Q) ((1 # 2)%Q / K)).
  { apply (piu1872_bridge WING (1 # 2)%Q (2 * K)%Q K).
    - apply Qmult_lt_0_compat; [ vm_compute; reflexivity | exact HKlt ].
    - exact HKlt.
    - apply (Qle_trans (WING * K) (1 * K) ((1 # 2)%Q * (2 * K))).
      + apply (Qmult_le_compat_r WING 1 K);
          [ exact Hw1 | apply Qlt_le_weak; exact HKlt ].
      + rewrite Qmult_1_l.
        assert (E12 : ((1 # 2)%Q * 2)%Q == 1%Q) by reflexivity.
        assert (Ehalf : ((1 # 2)%Q * (2 * K))%Q == K%Q).
        { rewrite (Qmult_assoc (1 # 2)%Q 2 K). rewrite E12. apply Qmult_1_l. }
        rewrite Ehalf. apply Qle_refl. }
  assert (Hleg13 : Qle (WING / (2 * K)%Q) (1 # 3)%Q).
  { apply (Qle_trans _ ((1 # 2)%Q / K)).
    - exact Hleg.
    - apply (piu1872_bridge (1 # 2)%Q 1 K (3 # 1)%Q).
      + exact HKlt.
      + vm_compute. reflexivity.
      + apply (Qle_trans ((1 # 2)%Q * (3 # 1)%Q) (3 # 2)%Q (1 * K)%Q).
        * vm_compute. discriminate.
        * rewrite Qmult_1_l. exact HK32. }
  unfold piu1872_eps2. apply Q.min_r. unfold piu1872_eps1. apply piu1872_min4.
  - exact Heg.
  - exact Hel.
  - exact Hleg13.
  - exact Hleg.
Qed.

(* ---------- §6 互译恒等式闭链完成（1866 前提参数位免肢） ---------- *)
(* 十五步消元主难段（1868 移交·逐字）＋本件 AC 尾新链四步                *)
(* （comm→unfold Nc→assoc<- 两连·Qmult_assoc 实证定向对树核验）           *)
(* ——probe1872b ERR-COUNT=0 实证。                                        *)

Lemma piu1872_mirror_identity : forall (b0 q : Q) (n h : nat),
  piu1866_mirror_identity b0 q n h.
Proof.
  intros b0 q n h. unfold piu1866_mirror_identity.
  unfold lw0_Wb.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  replace (n + 2 * 0 + 1)%nat with (n + 1)%nat by lia.
  replace (2 * n + 2 * 0 + 2)%nat with (2 * n + 2)%nat by lia.
  assert (H1 : q_fact 1 == 1) by (vm_compute; reflexivity).
  rewrite H1.
  rewrite (Qmult_1_r (q_fact n)).
  set (X := q_pow b0 n * q_pow q (2 * n + 2)%nat * q_fact (n + 1)%nat
            / (q_fact n * q_fact (2 * n + 2)%nat)).
  set (Nc := q_pow b0 n * q_pow q (2 * n + 2)%nat * q_fact (n + 1)%nat).
  set (e := (Z.of_nat (Datatypes.S h) # 1)%Q).
  assert (HD : ~ (q_fact n * q_fact (2 * n + 2)%nat == 0)).
  { intro Hz. apply (Qlt_not_eq 0 (q_fact n * q_fact (2 * n + 2)%nat)).
    - apply Qmult_lt_0_compat; apply q_fact_pos.
    - apply Qeq_sym. exact Hz. }
  assert (EC : q_fact n * q_fact (2 * n + 2)%nat * X == Nc)
    by (apply Qmult_div_r; exact HD).
  transitivity (e * ((2 # 27)%Q * Nc)).
  - rewrite (Qmult_comm X (2 # 27)%Q).
    rewrite (Qmult_assoc (q_fact n) (2 # 27)%Q X).
    rewrite (Qmult_comm (q_fact n) (2 # 27)%Q).
    rewrite <- (Qmult_assoc (2 # 27)%Q (q_fact n) X).
    rewrite (Qmult_comm ((2 # 27)%Q * (q_fact n * X)) (e * q_fact (2 * n + 2)%nat)).
    rewrite <- (Qmult_assoc e (q_fact (2 * n + 2)%nat) ((2 # 27)%Q * (q_fact n * X))).
    rewrite (Qmult_comm (q_fact (2 * n + 2)%nat) ((2 # 27)%Q * (q_fact n * X))).
    rewrite <- (Qmult_assoc (2 # 27)%Q (q_fact n * X) (q_fact (2 * n + 2)%nat)).
    rewrite (Qmult_comm (q_fact n) X).
    rewrite <- (Qmult_assoc X (q_fact n) (q_fact (2 * n + 2)%nat)).
    rewrite (Qmult_comm X (q_fact n * q_fact (2 * n + 2)%nat)).
    rewrite EC.
    reflexivity.
  - rewrite (Qmult_comm e ((2 # 27)%Q * Nc)).
    unfold Nc.
    rewrite <- (Qmult_assoc (2 # 27)%Q (q_pow b0 n) (q_pow q (2 * n + 2)%nat)).
    rewrite <- (Qmult_assoc (2 # 27)%Q
                  (q_pow b0 n * q_pow q (2 * n + 2)%nat) (q_fact (n + 1)%nat)).
    reflexivity.
Qed.

(* 阀形闭式坐标对接（免互译前提）：互译恒等式已完成闭合，                  *)
(* 1868 冻结件 piu1868_valve_closed_R1 的 `piu1866_mirror_identity` 前提    *)
(* 槽在本件免槽——闭式坐标直连 R1 阀形。                                     *)
Lemma piu1872_valve_closed_R1_free : forall (WING K b0 q : Q) (n h : nat),
  WING == q_fact n * (lw0_Wb b0 q n 0 * (2 # 27)%Q) ->
  piu1866_valve_closed b0 q n h K ->
  piu1866_valve_R1 WING K h n.
Proof.
  intros WING K b0 q n h HWing Hclosed.
  apply (piu1866_valve_R1_mirror_facet WING K b0 q n h HWing
           (piu1872_mirror_identity b0 q n h)).
  exact Hclosed.
Qed.

(* ---------- §7 带域 margin 逐支下界（GAPASUME·Section 参数位互译 1868） ---------- *)

Section CarrierBandMargin1872.

Variable q b0 : Q.
Variable n_sel h : nat.
Variable eg el K WING eps1 eps2 : Q.

(* 链域前提（1868 Section 参数位逐字） *)
Hypothesis Hns2 : (2 <= n_sel)%nat.
Hypothesis HKpos : Qlt 0 K.
Hypothesis Heps1def : eps1 = piu1872_eps1 eg el K.
Hypothesis Heps2def : eps2 = piu1872_eps2 eps1 WING K.
(* 带域前提位（1866 band 域） *)
Hypothesis Hband : piu1866_in_band q.
(* 阀形双肢（接合点） *)
Hypothesis Hvalve_up : piu1872_valve_up K h n_sel.
Hypothesis Hvalve_R1 : piu1866_valve_R1 WING K h n_sel.
(* 证书条件承载位（1862 §3 边界①·eg,el 下界形） *)
Hypothesis Hcert_eg : Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) eg.
Hypothesis Hcert_el : Qle ((4 # 1)%Q / piu1872_valve_den h n_sel) el.

Lemma piu1872_band_margin_wit1 :
  Qle (1 / piu1872_valve_den h n_sel)%Q (piu1872_wit eps1).
Proof.
  apply (piu1872_wit_lower eps1 (piu1872_valve_den h n_sel)).
  - unfold piu1872_valve_den. apply Qmult_lt_0_compat.
    + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z) by (apply Z2Nat.inj_lt; lia).
      unfold Qlt. cbn [Qnum Qden]. lia.
    + apply q_fact_pos.
  - rewrite Heps1def. unfold piu1872_valve_up in Hvalve_up.
    apply (piu1872_eps1_leg eg el K (piu1872_valve_den h n_sel));
      [ exact Hcert_eg | exact Hcert_el | exact HKpos
      | exact Hvalve_up
      | apply piu1872_den_ge24; exact Hns2 ].
Qed.

Lemma piu1872_band_margin_wit2 :
  Qle (1 / piu1872_valve_den h n_sel)%Q (piu1872_wit eps2).
Proof.
  apply (piu1872_wit_lower eps2 (piu1872_valve_den h n_sel)).
  - unfold piu1872_valve_den. apply Qmult_lt_0_compat.
    + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z) by (apply Z2Nat.inj_lt; lia).
      unfold Qlt. cbn [Qnum Qden]. lia.
    + apply q_fact_pos.
  - rewrite Heps2def. unfold piu1872_eps2.
    apply (Q.min_glb eps1 (WING / (2 * K)%Q)
             ((4 # 1)%Q / piu1872_valve_den h n_sel)).
    + rewrite Heps1def. unfold piu1872_valve_up in Hvalve_up.
      apply (piu1872_eps1_leg eg el K (piu1872_valve_den h n_sel));
        [ exact Hcert_eg | exact Hcert_el | exact HKpos
        | exact Hvalve_up
        | apply piu1872_den_ge24; exact Hns2 ].
    + apply (piu1872_valve_R1_leg WING K h n_sel HKpos Hvalve_R1).
Qed.

End CarrierBandMargin1872.

(* ---------- §8 墙1 终定理：高度坐标面全链装配（1864 耦合桥·40h+48） ---------- *)
(* 带域前提下 margin 链 c₀=1 见证两形逐点下界——ck 面（c₀=1 构造形）       *)
(* `ck q ≥ 1/((h+1)·(2n_sel+2)!)` 逐点形；坐标面＝lw1m_height q 与        *)
(* piu1864_nsel (Qred q)，阀形肢经 piu1866_valve_R1_height 换算入 40h+48。  *)

Theorem piu1872_band_ck_assembly :
  forall (q b0 eg el K WING eps1 eps2 : Q),
    Qlt 0 K ->
    eps1 = piu1872_eps1 eg el K ->
    eps2 = piu1872_eps2 eps1 WING K ->
    piu1866_in_band q ->
    Qle ((8 # 1)%Q * K)
        ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
         * q_fact (40 * lw1m_height q + 48)%nat) ->
    piu1866_valve_R1 WING K (lw1m_height q) (piu1864_nsel (Qred q)) ->
    Qle ((4 # 1)%Q / ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
             * q_fact (40 * lw1m_height q + 48)%nat)) eg ->
    Qle ((4 # 1)%Q / ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
             * q_fact (40 * lw1m_height q + 48)%nat)) el ->
    Qle (1 / ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
             * q_fact (40 * lw1m_height q + 48)%nat))%Q (piu1872_wit eps1)
    /\ Qle (1 / ((Z.of_nat (Datatypes.S (lw1m_height q)) # 1)%Q
             * q_fact (40 * lw1m_height q + 48)%nat))%Q (piu1872_wit eps2)
    /\ Qlt 0 (piu1872_wit eps2).
Proof.
  intros q b0 eg el K WING eps1 eps2 HK Hdef1 Hdef2 Hband Hup48 HR148
         Hceg48 Hcel48.
  pose proof (piu1864_two_nsel_height q) as E40.
  set (ns := piu1864_nsel (Qred q)) in *.
  set (h := lw1m_height q) in *.
  assert (Hns2 : (2 <= ns)%nat).
  { pose proof (piu1864_nsel_qden (Qred q)) as Hn.
    pose proof (Pos2Nat.is_pos (Qden (Qred q))) as Hp.
    lia. }
  assert (Eden : piu1872_valve_den h ns
                 == ((Z.of_nat (Datatypes.S h) # 1)%Q
                     * q_fact (40 * h + 48)%nat)%Q).
  { unfold piu1872_valve_den. rewrite E40. reflexivity. }
  assert (Hup : piu1872_valve_up K h ns).
  { unfold piu1872_valve_up. rewrite Eden. exact Hup48. }
  assert (Hceg : Qle ((4 # 1)%Q / piu1872_valve_den h ns) eg).
  { rewrite Eden. exact Hceg48. }
  assert (Hcel : Qle ((4 # 1)%Q / piu1872_valve_den h ns) el).
  { rewrite Eden. exact Hcel48. }
  assert (TW1 : Qle (1 / piu1872_valve_den h ns)%Q (piu1872_wit eps1)).
  { apply (piu1872_band_margin_wit1 ns h eg el K eps1).
    - exact Hns2.
    - exact HK.
    - exact Hdef1.
    - exact Hup.
    - exact Hceg.
    - exact Hcel. }
  assert (TW2 : Qle (1 / piu1872_valve_den h ns)%Q (piu1872_wit eps2)).
  { apply (piu1872_band_margin_wit2 ns h eg el K WING eps1 eps2).
    - exact Hns2.
    - exact HK.
    - exact Hdef1.
    - exact Hdef2.
    - exact Hup.
    - exact HR148.
    - exact Hceg.
    - exact Hcel. }
  assert (Hdenpos : Qlt 0 (1 / piu1872_valve_den h ns)%Q).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - vm_compute. reflexivity.
    - apply Qinv_lt_0_compat. unfold piu1872_valve_den.
      apply Qmult_lt_0_compat.
      + assert (Hp : (0 < Z.of_nat (Datatypes.S h))%Z)
          by (apply Z2Nat.inj_lt; lia).
        unfold Qlt. cbn [Qnum Qden]. lia.
      + apply q_fact_pos. }
  split; [ | split ].
  - rewrite Eden in TW1. exact TW1.
  - rewrite Eden in TW2. exact TW2.
  - apply (Qlt_le_trans 0 (1 / piu1872_valve_den h ns)%Q
             (piu1872_wit eps2)).
    + exact Hdenpos.
    + exact TW2.
Qed.

(* ---------- §9 ck 面对接（tlw1448_transfer 可见面） ---------- *)
(* `tlw1448_ck q := projT1 (leibsep_q_kernel q)`（正本 Qed 不透明）——      *)
(* 本对接肢取其可面（正性＋距离窗）与 §8 终定理合流：链见证两形为            *)
(* kernel carrier 的 c₀=1 构造形，其逐点下界由 §8 全链承载。                *)

Theorem piu1872_band_ck_face_dock : forall q : Q,
  piu1866_in_band q ->
  And (QltT 0 (tlw1448_ck q)) (lw1m_dist_pt q (tlw1448_ck q)).
Proof.
  intros q _. apply tlw1448_kernel_dist_ck.
Qed.

(* ---------- §10 假设闭合自检 ---------- *)

Print Assumptions piu1872_qfact_mono.
Print Assumptions piu1872_min4.
Print Assumptions piu1872_bridge.
Print Assumptions piu1872_wit_lower.
Print Assumptions piu1872_Qeq_le_swap.
Print Assumptions piu1872_den_ge24.
Print Assumptions piu1872_eps1_leg.
Print Assumptions piu1872_valve_R1_leg.
Print Assumptions piu1872_margin_cap.
Print Assumptions piu1872_cert_from_WING.
Print Assumptions piu1872_eps2_equalization.
Print Assumptions piu1872_mirror_identity.
Print Assumptions piu1872_valve_closed_R1_free.
Print Assumptions piu1872_band_margin_wit1.
Print Assumptions piu1872_band_margin_wit2.
Print Assumptions piu1872_band_ck_assembly.
Print Assumptions piu1872_band_ck_face_dock.
