(* ============================================================ *)
(* UpAblZpos.v —— 假设消融战役 AB1 席（N-1+N-2 同席）                  *)
(*   B4 Z_align_pos 抽象接口层 discharge ＋ B8 sum_over_S_pos 连带收割。 *)
(*                                                              *)
(* 母本：S05_AlignmentGRPO.v（原树零改，只读消费）。槽位两处同族：         *)
(*   主节 Section Alignment L54（Variable Z_align_pos : lt zero Z_align， *)
(*   Z_align 定义 L50-53）；迭代节 Section U2FixedPoint L4598（消费面     *)
(*   同一导出形 Z_align reward beta beta_pos pi_ref）。B8 槽=L2535/4602。 *)
(*                                                              *)
(* 语句形（诚实打包形）：接口面 S01:1399-1430 实测 sum_over_S 仅有        *)
(*   linear/add/ext/le/nonneg/zero_nonneg/abs 族字段——strict 求和正性     *)
(*   字段缺席，逐项正⟹和正的最后一步在本层不可推出（E398 B4 判据承续）。  *)
(*   故按 S8 接口零实例槽打包先例交付：B8 槽实形（S05 L2535              *)
(*   forall f, (forall s, lt zero (f s)) -> lt zero (sum_over_S f)）      *)
(*   作为显式 forall 前件打包，B4 槽语句在此前件下 discharge。            *)
(*   接口面可证部分（nonneg 伴件）另件全量兑现，见 zab_Z_align_nonneg。    *)
(*                                                              *)
(* 非平凡内容：求和项逐项正链（zab_summand_pos）——pi_ref_pos 逐点正      *)
(*   × exp_neg_pos 恒正（S01:180 基础接口字段）经 mult_positive          *)
(*   （S01:223 增强接口字段）合成，且经 inv_pos beta beta_pos 换形，      *)
(*   与 S05 L2546-2551 Z_rel_pos 证明链同构。                            *)
(*                                                              *)
(* 升级方向：接口补 strict 求和正性字段（或 Real 层实例以 sumd 引擎      *)
(*   sumd_sum_pos 直装，G12 zpfinal 族 req 层先例），打包前件即消。       *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层 / 原树零改 / zab_ 前缀本件防撞 /      *)
(*       零承认件（本件头注即无英文禁词字面）。                          *)
(* ============================================================ *)

Require Import S01_BaseRing.

Section ZabZPos.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let le := @le RI.
Let lt := @lt RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* S05 主节 L50-53 Z_align 出节实形同构（迭代节 L4598 消费同形）：      *)
(* Z_align := Σ_s pi_ref(s)·exp_neg(−r(s)/β)，beta_pos 为显式参。        *)
Definition zab_Z_align (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
           (pi_ref : S -> R) : R :=
  sum_over_S (fun s => mult (pi_ref s)
                            (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).

(* 求和项逐项正：pi_ref 逐点正 × exp_neg 恒正 → 乘积正（B4 核内容）。 *)
Lemma zab_summand_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
    forall s : S,
      lt zero (mult (pi_ref s)
                    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos s.
  apply mult_positive.
  - exact (pi_ref_pos s).
  - apply exp_neg_pos.
Qed.

(* 主件（诚实打包形）：Hsum_pos 即 B8 槽实形（S05 L2535/4602 逐字同形）   *)
(* 显式 forall 前件打包；B4 槽语句（lt zero Z_align，主节 L54/迭代节       *)
(* L4598 同族）在前件下 discharge。                                       *)
Theorem zab_Z_align_pos :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
         (Hsum_pos : forall f : S -> R,
                       (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f)),
    lt zero (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos Hsum_pos.
  unfold zab_Z_align.
  apply Hsum_pos.
  exact (zab_summand_pos reward beta beta_pos pi_ref pi_ref_pos).
Qed.

(* 接口面无条件伴件（打包面之外的接口可证部分全量兑现）：不求和正性       *)
(* 前件，仅耗 sum_over_S_nonneg 接口字段（S01:1418），逐项正经            *)
(* lt_le_iff 降非负得整体非负——le zero Z_align 无条件成立。              *)
Theorem zab_Z_align_nonneg :
  forall (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
         (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s)),
    le zero (zab_Z_align reward beta beta_pos pi_ref).
Proof.
  intros reward beta beta_pos pi_ref pi_ref_pos.
  unfold zab_Z_align.
  apply sum_over_S_nonneg.
  intro s.
  exact (lt_le_iff _ _
           (inl (zab_summand_pos reward beta beta_pos pi_ref pi_ref_pos s))).
Qed.

End ZabZPos.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions zab_summand_pos.
Print Assumptions zab_Z_align_pos.
Print Assumptions zab_Z_align_nonneg.
