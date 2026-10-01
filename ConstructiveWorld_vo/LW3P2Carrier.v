(* LW3P2Carrier.v                                                    *)
(* 使命：M3 主语句第二前提（K 面非零见证）的条件承载形装配——以多项式在    *)
(*       欧拉数处取零的实侧等词前件与实侧解析半边的显式承载位为前提，      *)
(*       经端点泛函求值式桥与 K-λ 谱桥完成布尔非零转移；另附锚例双向钉    *)
(*       （零例处承载位空化、锚例处承载位有驻且 K 见证实际产出）。        *)
(* 依赖：LW3ETranscendental（只读正本）及其闭包 S02/S03/LW0/LW1/LW2 系；  *)
(*       LW3P2Prod（端点泛函求值式桥，只读使用）。                   *)
(* 对标：E-STAGING-LW3-PROBEPIN；E-STAGING-LW3-KNZWALL；                  *)
(*       E-STAGING-LW0-GAPASUME（余留缺口显式前提位承载，命名避占终形）；  *)
(*       kleg377 空化判例（无条件一般形之反例在件）。                     *)
(* 构造性：语句面全 Set（非零多项式见证 sigT 数据形、实侧等词数据形       *)
(*       real_eq、见证型 Qnz 前后两端），语句与前提位零 Prop；证明体等词  *)
(*       面沿主语句证明体 assert 先例口径；提取并集数据名，魔数=0；       *)
(*       禁引六族零命中。                                                 *)
(* 编译配方：coqc 全路径 -q -Q . "" -Q ConstructiveWorld-Main/            *)
(*       ConstructiveWorld_vo ""，cpu_guard 包裹，SW2 双 export 全字面。 *)
Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW0FactGrowth.
Require Import LW2UpperBound.
Require Import LW2NivenInt.
Require Import LW3ETranscendental.
Require Import LW3P2Prod.

(* The rational-side transfer: the nonvanishing witness rides the two      *)
(* bridges.  The spec bridge ties the integer functional value to the      *)
(* node functional, and the evaluation bridge ties the node functional to  *)
(* the endpoint value with unit exponential scalar.  Should the integer    *)
(* value decide equal to zero, both bridges would force the endpoint value *)
(* to zero and the handed-over witness would empty; hence the decidable    *)
(* comparison takes the false branch and the witness is produced.          *)
Lemma tlw379_qtransfer :
  forall (p : zpoly) (N : nat),
    lw3_qnz (lw2_exp_L (1 # 1)%Q
              (length (lw3_fbuild p (lw3_deg p) N))
              (lw3_fbuild p (lw3_deg p) N)
              (lw2_node (Datatypes.S (lw3_nodecount p N)))) ->
    lw3_qnz ((lw3_Kinst p N) # 1)%Q.
Proof.
  intros p N Hgap.
  unfold lw3_qnz in Hgap.
  unfold lw3_qnz.
  destruct (Qeq_bool ((lw3_Kinst p N) # 1)%Q 0%Q) eqn:HKq.
  - apply Qeq_bool_eq in HKq.
    pose proof (lw3_Kinst_spec p N) as Es.
    pose proof (tlw229_lam_expL (lw3_nodecount p N)
                  (lw3_fbuild p (lw3_deg p) N)) as Eb.
    apply qeqT_imp_qeq in Eb.
    assert (Hlam0 : lw2_lambda (lw3_nodecount p N)
                      (lw3_fbuild p (lw3_deg p) N) == 0%Q).
    { exact (Qeq_trans _ _ _ Es HKq). }
    assert (Hexp0 : lw2_exp_L (1 # 1)%Q
                      (length (lw3_fbuild p (lw3_deg p) N))
                      (lw3_fbuild p (lw3_deg p) N)
                      (lw2_node (Datatypes.S (lw3_nodecount p N))) == 0%Q).
    { exact (Qeq_trans _ _ _ (Qeq_sym _ _ Eb) Hlam0). }
    rewrite (Qeq_eq_bool _ _ Hexp0) in Hgap.
    exact Hgap.
  - exact tt.
Qed.

(* The conditional carrier: the nonzero polynomial witness, the vanishing *)
(* of the polynomial evaluation at the constructive constant e carried in *)
(* the real-side equality data, and the explicit standing premise holding *)
(* the real-side analytic half (the derivation of the endpoint value's    *)
(* nonvanishing from the vanishing premise belongs to the continuation    *)
(* order) together produce the K witness.  All premises are Set-sorted.   *)
Theorem tlw379_p2carrier :
  forall (p : zpoly) (N : nat),
    lw3_nz p ->
    real_eq (lw3_evalr p lw3_e) real_zero ->
    lw3_qnz (lw2_exp_L (1 # 1)%Q
              (length (lw3_fbuild p (lw3_deg p) N))
              (lw3_fbuild p (lw3_deg p) N)
              (lw2_node (Datatypes.S (lw3_nodecount p N)))) ->
    lw3_qnz ((lw3_Kinst p N) # 1)%Q.
Proof.
  intros p N Hnz Hpzero Hgap.
  exact (tlw379_qtransfer p N Hgap).
Qed.

(* The anchor datum 1 + t: its node functional value is -265, so the      *)
(* standing premise is inhabited by direct computation, and the carrier   *)
(* chain produces the K witness at the first exponent instance even though*)
(* the integer value itself sits behind an opaque integral bridge.        *)
Definition p379b : zpoly := cons 1%Z (cons 1%Z nil).
Definition p379b_nz : lw3_nz p379b := existT _ 0%nat tt.

Definition tlw379_gap_p379b :
  lw3_qnz (lw2_exp_L (1 # 1)%Q
            (length (lw3_fbuild p379b (lw3_deg p379b) 1))
            (lw3_fbuild p379b (lw3_deg p379b) 1)
            (lw2_node (Datatypes.S (lw3_nodecount p379b 1)))) := tt.

Theorem tlw379_p2inst : lw3_qnz ((lw3_Kinst p379b 1) # 1)%Q.
Proof. exact (tlw379_qtransfer p379b 1 tlw379_gap_p379b). Qed.

(* The recorded zero instance -46 + 7 t empties the standing premise: its *)
(* endpoint functional value vanishes together with the node functional,  *)
(* so the conditional premise carries genuine content and is no trivially *)
(* available witness.                                                     *)
Theorem tlw379_gap_empty_p202 :
  lw3_qnz (lw2_exp_L (1 # 1)%Q
            (length (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1))
            (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)
            (lw2_node (Datatypes.S (lw3_nodecount lw3_p202 1)))) -> Empty_set.
Proof.
  intro H.
  assert (Eb : Qeq_bool (lw2_exp_L (1 # 1)%Q
                  (length (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1))
                  (lw3_fbuild lw3_p202 (lw3_deg lw3_p202) 1)
                  (lw2_node (Datatypes.S (lw3_nodecount lw3_p202 1))))
                0%Q = true)
    by (vm_compute; reflexivity).
  unfold lw3_qnz in H. rewrite Eb in H. exact H.
Qed.

Print Assumptions tlw379_qtransfer.
Print Assumptions tlw379_p2carrier.
Print Assumptions tlw379_p2inst.
Print Assumptions tlw379_gap_empty_p202.

Separate Extraction p379b.
