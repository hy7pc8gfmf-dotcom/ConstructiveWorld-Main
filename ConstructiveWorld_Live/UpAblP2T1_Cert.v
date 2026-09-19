(* ============================================================ *)
(* UpAblP2T1_Cert.v —— A1 席（论文2 T 簇证书供给席）                        *)
(*   论文2 T 簇合并单 28 行·T 级合并申报供给件（新独立批件）                  *)
(* 工单：attn\_ts1_论文2登记收割报告-20260920.md §四（25 位逐位表＋P2A T1-T3） *)
(* 模板体例：UpAblP1T1_AlignCert.v／UpAblP1T2_GrpoAuditCert.v（判例行 :50/:100）*)
(* 原树零改：S15/S04/S06/S08/AttnDoeblin/UpKVDrift/UpRealLeB/UpReqTempDefs/  *)
(*   UpReqPowMonoBridge 全部只读消费；不入 order.txt/_CoqProject；           *)
(*   禁触 9.0 任何产物。                                                     *)
(*                                                              *)
(* 逐位供给账（坐标＝S1 报告实测；「补」＝P2B 未给坐标处 S1 新测）：          *)
(*   行 1  T_pos          S15:54-55   → p2t1_T_pos_supply（段二·核直引）     *)
(*   行 2  T              S15:54      → p2t1_T_supply（载体定义＋见证配对）  *)
(*   行 3  D_pos          S04:1888/:2002 → p2t1_D_pos_supply（段二）         *)
(*   行 4  Z_pos          S04:1891/:2012 → p2t1_Z_pos_supply（段五·B27 直引形）*)
(*   行 5  Z_thermo_pos   S06:3854    → p2t1_Z_thermo_pos_supply（段五·同上） *)
(*   行 6  Delta_pos（补） AttnDoeblin:458 → p2t1_Delta_pos_supply（段二）   *)
(*   行 7  temp_pos       S15:142     → p2t1_temp_pos_supply（段二）         *)
(*   行 8  evicted_partition_pos S06:4625 → p2t1_evicted_partition_pos_supply *)
(*                                       （段三·单点世界 one_pos 直引）      *)
(*   行 9  topk_kept_partition_pos S06:5554 → p2t1_topk_kept_partition_pos_  *)
(*                                       supply（段三·同上）                 *)
(*   行 10 min_p_pos      S06:6128/:7405 → p2t1_min_p_pos_supply（段二）     *)
(*   行 11 min_p_lt_one   S06:6129/:7406 → p2t1_min_p_lt_one_supply（段二·   *)
(*                                       B7 形核）                           *)
(*   行 12 temperature_pos S06:3083/:5954/:7142 → p2t1_temperature_pos_supply *)
(*   行 13 vocab_nonempty S06:3077/:5950/:7138 → p2t1_vocab_nonempty_supply  *)
(*                                       （段四·二元枚举载体直构）           *)
(*   行 14 S_finite_cover S06:4969    → p2t1_S_finite_cover_supply（段四·   *)
(*                                       InT_here/next 递推直构）            *)
(*   行 15 K              S06:4967    → p2t1_K_supply＋leb 镜像＋of_nat 正性  *)
(*                                       （段四·B17 形）                     *)
(*   行 16 topk_pickmax_head S06:7627 → p2t1_topk_pickmax_head_pack（段五· *)
(*                                       打包形；(1<=K) 前件以 Nat.leb Set 层 *)
(*                                       镜像收拢，证明面 Nat.leb_le 桥）    *)
(*   行 17 spp            S15:56-58   → p2t1_spp_supply（段三·单点世界构造  *)
(*                                       性供给，非仅打包）                  *)
(*   行 18 q_pos（补）    S06:225     → p2t1_q_pos_supply（段二·常值函数载体）*)
(*   行 19 q_norm（补）   S06:235     → p2t1_q_norm_pack（段五·接口面不可构  *)
(*                                       造，显式前件收拢，p1t2 B12 同形）   *)
(*   行 20 default_token（补）S06:5955/:7143 → p2t1_default_token_supply     *)
(*                                       （段四·常数载体逐点平凡供给）       *)
(*   行 21 Hrow           UpKVDrift:190（:189 c 配对）→ p2t1_Hrow_pack＋     *)
(*                                       p2t1_Hrow_c_supply（段五·c 取常数   *)
(*                                       载体 real_one）                     *)
(*   行 22 Z_temp_spec    S04:3416    → p2t1_Z_temp_pos_supply（段五·       *)
(*                                       real_Z_temp_pos@UpReqTempDefs:116   *)
(*                                       在库直引；spec 面为定义性恒等式注记）*)
(*   行 23 inv_pos_lt_compat S04:3341 → p2t1_inv_pos_lt_compat_pack（段五·  *)
(*                                       显式前件收拢；req 系同名字段镜像）   *)
(*   行 24 lt_minus_nonneg S04:3343   → p2t1_lt_minus_nonneg_supply（段二·  *)
(*                                       real_lt 逐点展开，real_const 对）   *)
(*   行 25 real_minp_temp_sum_pos（补）S08:2175 → p2t1_real_minp_temp_sum_  *)
(*                                       pos_pack（段五·显式前件收拢）       *)
(*                                                              *)
(* 升格位（P2A T1-T3）：                                                    *)
(*   T1 kv_drift_bound plain-eps→Bishop 升格：p2t1_kv_drift_bound_B（段六·  *)
(*      real_le_closure_b_one@UpRealLeB:381 单步直连，D:=one 证书            *)
(*      real_lt_zero_one 既有；kv_drift_bound 出节签名两发探针实测）         *)
(*   T2 UpRealLeB 结论 9(e)/(f) 复合/多 eps 形升格面：【挂账】——源件面实测   *)
(*      real_abs_le_quad_eps@S08:4901 五前件＋四分支内件链，UpRealLeB 尾注   *)
(*      自书「可升格但证书链长且语句须前提位改造——未建（非冻结）」；         *)
(*      结论 10 的 16+2 件 plain-eps 面已由 Part E 席收口（禁重做）。        *)
(*      非平凡面如实挂账候续席，本席不虚报 T 级。                            *)
(*   T3 le_b 乘法因子纯 B 形无上界版：常数对直引形已供                       *)
(*      p2t1_x3d_le_b_mult_one（段六·x3d_le_b_mult_r_pos＋real_lt_zero_one）  *)
(*      ＋任意非负 Or 形因子直引形 p2t1_x3d_le_b_mult_r；「纯 B 形无上界版」  *)
(*      构造性不可通如实注记（UpReqPowMonoBridge 件4 自书：B 形非负⟹Or 形    *)
(*      反向构造性不通，因子无上界 M 时 eps 乘出无法压回——真墙域登记非欠账） *)
(*                                                              *)
(* 纪律：纯构造性零承认件／语句面全 Set 层（Id/Not/Or/And:=A*B/sigT/InT/     *)
(*   QltT/real_lt/real_le/real_eq/real_le_b/Nat.leb 别名面，裸命题零入语句   *)
(*   与前件位）／公理面零新增／原树零改／前缀 p2t1_ 防撞；                   *)
(*   一件多引理合并申报，T 级零虚报（挂账位如实注记）。                      *)
(* 四关留痕：attn/logs/p2t1-g{1..4}-UpAblP2T1_Cert.log；G3 提取一人一目录    *)
(*   _tp2t1_g3out（验后判读 Obj.magic 计数）。                               *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblT13c_G13.
Require Import UpRealLeB.
Require Import UpKVDrift.
Require Import UpReqTempDefs.
Require Import UpReqPowMonoBridge.
From Stdlib Require Import Extraction.

(* ################ 段一：Real 载体证书共享核（p1t1 B3/B7 体例重铸） ######### *)
(* 判例：p1t1_beta_pos_supply@UpAblP1T1_AlignCert.v:50／p1t1_eta_le_one_     *)
(* supply@:100（S1 报告判例行实测吻合）。real_lt 逐点展开，eps:=q/2；        *)
(* Q 层乘法保序走全参显式项。束间共享核，逐位行以具名引理直引收拢。          *)

Theorem p2t1_pos_const_core : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof.
  intros q Hq.
  assert (Hq' : Qlt (0#1)%Q q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  unfold real_lt.
  exists (q * (1#2)%Q).
  split.
  - apply Qlt_to_QltT.
    assert (H2 : Qlt (0 * (1#2)%Q) (q * (1#2)%Q)).
    { exact (Qmult_lt_compat_r 0%Q q (1#2)%Q H02 Hq'). }
    setoid_rewrite Qmult_0_l in H2. exact H2.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hc. setoid_rewrite Hz.
    assert (Hr1 : (q - 0)%Q == (1#1)%Q * q) by ring. setoid_rewrite Hr1.
    assert (Hr2 : q * (1#2)%Q == (1#2)%Q * q) by ring. setoid_rewrite Hr2.
    exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q q Hq' Hhalf).
Qed.

Theorem p2t1_le_one_const_core : forall q : Q, QltT q (1#1)%Q ->
  real_le (real_const q) real_one.
Proof.
  intros q Hq.
  assert (Hq' : Qlt q (1#1)%Q) by (apply QltT_to_Qlt; exact Hq).
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  assert (H0m : Qlt 0%Q (1 - q)%Q)
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (H0 : Qlt 0 ((1#1)%Q + (- q)))
    by exact (proj1 (Qlt_minus_iff q (1#1)%Q) Hq').
  assert (Hlt : real_lt (real_const q) real_one).
  { unfold real_lt.
    exists ((1 - q) * (1#2)%Q)%Q.
    split.
    - apply Qlt_to_QltT.
      assert (H2a : Qlt (0 * (1#2)%Q) ((1 - q)%Q * (1#2)%Q)).
      { exact (Qmult_lt_compat_r 0%Q (1 - q)%Q (1#2)%Q H02 H0m). }
      setoid_rewrite Qmult_0_l in H2a. exact H2a.
    - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
      assert (Hc : projT1 (real_const q) n == q) by (apply real_const_proj).
      assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
      setoid_rewrite Hc. setoid_rewrite Ho.
      assert (HrB : (1 - q)%Q == (1#1)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrB at 2.
      assert (HrA : (1 - q)%Q * (1#2)%Q
                    == (1#2)%Q * ((1#1)%Q + (- q))) by ring.
      setoid_rewrite HrA.
      exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q ((1#1)%Q + (- q)) H0 Hhalf). }
  unfold real_le.
  exact (@inl (real_lt (real_const q) real_one)
              (real_eq (real_const q) real_one) Hlt).
Qed.

(* 端点双供（p1t1 端点形同款） *)
Theorem p2t1_one_pos_lt : real_lt real_zero real_one.
Proof. exact real_lt_zero_one. Qed.

Theorem p2t1_one_le_one : real_le real_one real_one.
Proof. exact (real_le_refl real_one). Qed.

(* ################ 段二：逐位供给·正性数据位行（核直引收拢） ############### *)
(* 行 1/2：S15:54-55 T／T_pos（FEPAttention 温度数据位＋正性配对）。          *)
(* 行 3：S04:1888/:2002 D_pos（热力学温度正性，两区段同形）。                *)
(* 行 6：AttnDoeblin:458 Delta_pos（双界 logits 上界正性，LoHiSqueeze 组）。 *)
(* 行 7：S15:142 temp_pos（RowView 区 12 位组）。                            *)
(* 行 10：S06:6128/:7405 min_p_pos（Min-P 超参正性，两节各一套，一证双覆盖）。*)
(* 行 12：S06:3083/:5954/:7142 temperature_pos（采样温度正性三区段）。        *)
(* 行 18：S06:225 q_pos（补测；参考策略逐点正——常值函数载体）。              *)
(* 行 11：S06:6129/:7406 min_p_lt_one（Min-P 上界位——B7 形核）。             *)
(* 行 24：S04:3343 lt_minus_nonneg（序差正性——real_lt 逐点展开）。           *)

Theorem p2t1_T_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

(* 行 2 载体：T 取正有理常数载体（配对申报） *)
Definition p2t1_T_c (q : Q) : Real := real_const q.

Theorem p2t1_T_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (p2t1_T_c q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_D_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_Delta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_temp_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_min_p_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

Theorem p2t1_temperature_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (real_const q).
Proof. intros q Hq. exact (p2t1_pos_const_core q Hq). Qed.

(* 行 18：q 取常值函数载体，逐点正性由核直引（贝塔可逆） *)
Theorem p2t1_q_pos_supply : forall (q : Q), QltT (0#1)%Q q ->
  forall (S0 : Set) (s : S0),
    real_lt real_zero ((fun _ : S0 => real_const q) s).
Proof. intros q Hq S0 s. exact (p2t1_pos_const_core q Hq). Qed.

(* 行 11：min_p 取 (0,1) 内有理见证，≤一由 B7 形核直引 *)
Theorem p2t1_min_p_lt_one_supply : forall q : Q, QltT q (1#1)%Q ->
  real_le (real_const q) real_one.
Proof. intros q Hq. exact (p2t1_le_one_const_core q Hq). Qed.

(* 行 24：real_const 对的序差正性（real_minus_r a b := real_plus a (real_opp b) *)
(*   @S12:13234 逐点透明：q2 + (−q1) − 0 ＝ q2 − q1；eps := (q2−q1)/2 展开） *)
Theorem p2t1_lt_minus_nonneg_supply : forall q1 q2 : Q, QltT q1 q2 ->
  real_lt real_zero (real_minus_r (real_const q2) (real_const q1)).
Proof.
  intros q1 q2 Hq.
  assert (Hq' : Qlt q1 q2) by (apply QltT_to_Qlt; exact Hq).
  assert (H0m : Qlt 0%Q (q2 - q1)%Q)
    by exact (proj1 (Qlt_minus_iff q1 q2) Hq').
  assert (H02t : QltT 0%Q (1#2)%Q) by (unfold QltT; reflexivity).
  assert (H02 : Qlt 0%Q (1#2)%Q) by (apply QltT_to_Qlt; exact H02t).
  assert (Hhalft : QltT (1#2)%Q (1#1)%Q) by (unfold QltT; reflexivity).
  assert (Hhalf : Qlt (1#2)%Q (1#1)%Q) by (apply QltT_to_Qlt; exact Hhalft).
  unfold real_lt.
  exists ((q2 - q1) * (1#2)%Q)%Q.
  split.
  - apply Qlt_to_QltT.
    assert (H2a : Qlt (0 * (1#2)%Q) ((q2 - q1)%Q * (1#2)%Q)).
    { exact (Qmult_lt_compat_r 0%Q (q2 - q1)%Q (1#2)%Q H02 H0m). }
    setoid_rewrite Qmult_0_l in H2a. exact H2a.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    assert (Hy : projT1 (real_minus_r (real_const q2) (real_const q1)) n
                 == (q2 - q1)%Q).
    { unfold real_minus_r, real_plus, real_opp.
      cbn [projT1 real_const].
      try setoid_rewrite (real_const_proj q2 n).
      try setoid_rewrite (real_const_proj q1 n).
      ring. }
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    setoid_rewrite Hy. setoid_rewrite Hz.
    assert (Hr1 : (q2 - q1)%Q - 0 == (1#1)%Q * (q2 - q1)) by ring.
    setoid_rewrite Hr1.
    assert (HrC : (q2 - q1)%Q * (1#2)%Q == (1#2)%Q * (q2 - q1)) by ring.
    setoid_rewrite HrC.
    exact (Qmult_lt_compat_r (1#2)%Q (1#1)%Q (q2 - q1) H0m Hhalf).
Qed.

(* ################ 段三：单点 SumOver 实例世界行（T13c 载体） ############### *)
(* 世界：uab_ssUnit＋uab_soUnit（全库唯一具体 SumOver 实例，                  *)
(*   UpAblT13c_G13.v:41/:71）：和退化为核元素取值。                          *)
(* 行 17：spp（S15:56-58 求和正性函数前件）——单点世界上构造性成立：          *)
(*   和恒等于 f 于唯一点，前件逐点正直取。                                   *)
(* 行 8/9：evicted_partition_pos（S06:4625）／topk_kept_partition_pos        *)
(*   （S06:5554）——保留判定取常真、保留分支取常一，配分和即一，             *)
(*   one_pos 直引（p1t2 B11 形单点世界兑现）。                                *)

Theorem p2t1_spp_supply : forall (RI0 : RealInterfaceEnhanced)
    (f : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0),
    (forall s : @S RI0 (@uab_ssUnit (@RI_base RI0)),
       @lt RI0 (@zero RI0) (f s)) ->
    @lt RI0 (@zero RI0)
      (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0))
         (@uab_soUnit (@RI_base RI0)) f).
Proof.
  intros RI0 f H.
  exact (H (@uab_ssUnit_elem (@RI_base RI0))).
Qed.

(* 行 8 载体：保留判定常真＋保留分支常一的逐出配分（单点世界） *)
Definition p2t1_keep_true (RI0 : RealInterfaceEnhanced)
  (_ : @S RI0 (@uab_ssUnit (@RI_base RI0))) : bool := true.
Definition p2t1_bf_one (RI0 : RealInterfaceEnhanced)
  (_ : @S RI0 (@uab_ssUnit (@RI_base RI0))) : @R RI0 := @one RI0.
Definition p2t1_evict_part_c (RI0 : RealInterfaceEnhanced) : @R RI0 :=
  @sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
    (fun s : @S RI0 (@uab_ssUnit (@RI_base RI0)) =>
       if p2t1_keep_true RI0 s then p2t1_bf_one RI0 s else @zero RI0).

Theorem p2t1_evicted_partition_pos_supply : forall RI0 : RealInterfaceEnhanced,
  @lt RI0 (@zero RI0) (p2t1_evict_part_c RI0).
Proof. intro RI0. unfold p2t1_evict_part_c. exact (@one_pos RI0). Qed.

(* 行 9 载体：同形（top-k 保留判定常真） *)
Definition p2t1_topk_keep_true (RI0 : RealInterfaceEnhanced)
  (_ : @S RI0 (@uab_ssUnit (@RI_base RI0))) : bool := true.
Definition p2t1_topk_kept_part_c (RI0 : RealInterfaceEnhanced) : @R RI0 :=
  @sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
    (fun s : @S RI0 (@uab_ssUnit (@RI_base RI0)) =>
       if p2t1_topk_keep_true RI0 s then p2t1_bf_one RI0 s else @zero RI0).

Theorem p2t1_topk_kept_partition_pos_supply :
  forall RI0 : RealInterfaceEnhanced,
  @lt RI0 (@zero RI0) (p2t1_topk_kept_part_c RI0).
Proof. intro RI0. unfold p2t1_topk_kept_part_c. exact (@one_pos RI0). Qed.

(* ################ 段四：枚举载体世界行（B13/B15/B16/B17 形） ############### *)

(* 二元枚举集载体（p1t2_g2 同构，前缀防撞） *)
Inductive p2t1_tok : Set :=
| T0 : p2t1_tok
| T1 : p2t1_tok.

Definition p2t1_S_enum : list p2t1_tok := T0 :: T1 :: nil.

(* 行 13：vocab_nonempty（S06:3077/:5950/:7138 实形 Not (Id vocab nil)）—— *)
(*   二元枚举表直构（Not 为 S01 Set 层别名 A -> Empty_set）；索引取字面      *)
(*   构造子形＋空匹配机判消解（UpAblP2WByPass.v:185 先例体例，delta 可转换）*)
(*   重叠登记：:5950 面伴生件 p2wb_vocab_nonempty@UpAblP2WByPass.v:185 在库， *)
(*   本件为 T 簇行 13 具名证书申报，防重认领账照录不互斥。 *)
Theorem p2t1_vocab_nonempty_supply : Not (Id (cons T0 (cons T1 nil)) nil).
Proof. exact (fun h => match h with end). Qed.

(* 行 14：S_finite_cover（S06:4969 实形 forall s, InT s S_enum）—— *)
(*   枚举表两支递推直构（InT_here/InT_next；x/l 全显式参） *)
Theorem p2t1_S_finite_cover_supply : forall i : p2t1_tok, InT i p2t1_S_enum.
Proof.
  unfold p2t1_S_enum. intro i. destruct i as [| ].
  - apply InT_here.
  - apply InT_next. apply InT_here.
Qed.

(* 行 15：K（S06:4967 容量预算数据位，nat）——容量取一载体＋                 *)
(*   (1<=K) 的 Set 层 Nat.leb 镜像＋of_nat 逐字复刻正性（B17 形） *)
Definition p2t1_K_supply : nat := 1.

Theorem p2t1_K_leb_true : Id (Nat.leb 1 p2t1_K_supply) true.
Proof. exact id_refl. Qed.

(* 行 20：default_token（S06:5955/:7143 默认 token 数据位）——常数载体逐点平凡 *)
Definition p2t1_default_token_supply : p2t1_tok := T0.

Theorem p2t1_default_token_witness : Id p2t1_default_token_supply T0.
Proof. exact id_refl. Qed.

(* of_nat 逐字复刻（S05/S06 计数嵌入形；S01 顶层 S 遮蔽坑——用 Datatypes.S） *)
Section P2T1EnumPos.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let lt := @lt RI.
Let plus := @plus RI.

Fixpoint p2t1_of_nat (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S n' => plus one (p2t1_of_nat n')
  end.

(* 行 15 之 B17 形：枚举表长度二的嵌入＝一加一，正和字段直引 *)
Theorem p2t1_K_of_nat_pos :
  lt zero (p2t1_of_nat (length p2t1_S_enum)).
Proof.
  unfold p2t1_S_enum.
  apply (lt_id_r zero (plus one one)).
  - exact (id_cong (fun w : R => plus one w) (id_sym (plus_zero one))).
  - apply plus_positive.
    + exact one_pos.
    + exact one_pos.
Qed.

End P2T1EnumPos.

(* ################ 段五：接口前件行（B27 直引形／B12 打包收拢形） ########### *)
(* B27 直引形（p1t2 段四体例）：req 系 Setoid 语境，常量载体配分和正性。     *)
(* 行 4/5/23 三件（Setoid 语境）移段七置尾——Import RealInterfaceEnhancedMod  *)
(*   会遮蔽类字段投影（@one 转期望 Set 坑），p1t2 同款节序：@形件在前、       *)
(*   Setoid 节在尾。                                                        *)

(* 行 19：q_norm（S06:235 补测实形 Id (sum_over_S q) one）——接口面不可构造， *)
(*   显式前件收拢（p1t2 B12 同形；具体载体放电先例＝req 层 boltzmann 归一化件） *)
Theorem p2t1_q_norm_pack : forall (RI0 : RealInterfaceEnhanced)
    (SS0 : StateSpace RI0) (SO0 : SumOver RI0 SS0) (q : @S RI0 SS0 -> @R RI0),
    Id (@sum_over_S RI0 SS0 SO0 q) (@one RI0) ->
    Id (@sum_over_S RI0 SS0 SO0 q) (@one RI0).
Proof. intros RI0 SS0 SO0 q Hn. exact Hn. Qed.

(* 行 16：topk_pickmax_head（S06:7627 实形）——打包收拢；槽前件 (1 <= K)%nat  *)
(*   为裸命题面，以 Set 层 Nat.leb 镜像收拢（证明面 Nat.leb_le 双向桥），     *)
(*   keep/pick 以函数参量全称化（出节签名不可猜坑规避） *)
Theorem p2t1_topk_pickmax_head_pack :
  forall (Tok0 : Set)
         (keep : forall (K : nat) (prefix : list Tok0), Tok0 -> Set)
         (pick : list Tok0 -> Tok0),
    (forall (K : nat) (prefix : list Tok0),
       Id (Nat.leb 1 K) true -> keep K prefix (pick prefix)) ->
    forall (K : nat) (prefix : list Tok0),
       Id (Nat.leb 1 K) true -> keep K prefix (pick prefix).
Proof. intros Tok0 keep pick H K prefix HK. exact (H K prefix HK). Qed.

(* 行 21：Hrow（UpKVDrift:190，:189 c 配对）——c 取常数载体 real_one；       *)
(*   一致行误差前件以 tv_row 展开体（real_list_sum∘real_abs∘real_minus_r）    *)
(*   显式 forall 前件收拢（出节签名探针实测同构） *)
Definition p2t1_Hrow_c_supply : Real := real_one.

Theorem p2t1_Hrow_pack : forall (Tok0 : Set) (states : list Tok0)
    (Kk : Tok0 -> Tok0 -> Real) (kv : Tok0 -> Tok0 -> Real) (c : Real),
    (forall s : Tok0,
       real_le (real_list_sum Tok0
                  (fun s' : Tok0 => real_abs (real_minus_r (Kk s s') (kv s s')))
                  states) c) ->
    forall s : Tok0,
       real_le (real_list_sum Tok0
                  (fun s' : Tok0 => real_abs (real_minus_r (Kk s s') (kv s s')))
                  states) c.
Proof. intros Tok0 states Kk kv c Hrow s. exact (Hrow s). Qed.

(* 行 22：Z_temp_spec（S04:3416 槽形之 Real 定载对应面）——real_Z_temp_pos    *)
(*   @UpReqTempDefs:116 在库直引（五参泛化形，两发探针实测）；spec 恒等式面   *)
(*   ＝ real_Z_temp 定义性展开（定义件 1 头注自书「spec 退化定义性相等」）    *)
Theorem p2t1_Z_temp_pos_supply : forall (S0 : Type) (sumf : (S0 -> Real) -> Real),
    (forall f : S0 -> Real,
       (forall s : S0, real_lt real_zero (f s)) -> real_lt real_zero (sumf f)) ->
    forall (T : Real) (T_pos : real_lt real_zero T) (energy : S0 -> Real),
      real_lt real_zero (real_Z_temp S0 sumf T T_pos energy).
Proof.
  intros S0 sumf Hsum T T_pos energy.
  exact (real_Z_temp_pos S0 sumf Hsum T T_pos energy).
Qed.

(* 行 25：real_minp_temp_sum_pos（S08:2175 补测实形）——显式 forall 前件收拢  *)
(*   （截断和展开体逐字；保留判定取 Or/inl-inr S01 别名面，与 S08 同构） *)
Theorem p2t1_real_minp_temp_sum_pos_pack :
  forall (Token0 : Set) (vocab : list Token0) (tf : Token0 -> Real)
         (keep : list Token0 -> Token0 -> Set)
         (kdec : forall (prefix : list Token0) (w : Token0),
                   Or (keep prefix w) (Not (keep prefix w))),
    (forall prefix : list Token0,
       real_lt real_zero
         (real_list_sum Token0 (fun w : Token0 =>
            match kdec prefix w with
            | inl _ => tf w
            | inr _ => real_zero
            end) vocab)) ->
    forall prefix : list Token0,
       real_lt real_zero
         (real_list_sum Token0 (fun w : Token0 =>
            match kdec prefix w with
            | inl _ => tf w
            | inr _ => real_zero
            end) vocab).
Proof. intros Token0 vocab tf keep kdec Hsum prefix. exact (Hsum prefix). Qed.

(* ################ 段六：P2A T1-T3 升格位 ################################ *)

(* T1：kv_drift_bound（UpKVDrift:2170）plain-eps→Bishop 升格——               *)
(*   real_le_closure_b_one（UpRealLeB:381，D:=one 特化，证书 real_lt_zero_    *)
(*   one 既有）单步直连；出节签名两发探针实测（Not/And/sigT 全 Set 别名面）。 *)
Theorem p2t1_kv_drift_bound_B :
  forall (Tok0 : Set) (states : list Tok0) (Hne : Not (Id states nil))
         (K : Tok0 -> Tok0 -> Real)
         (HKnorm : forall s : Tok0,
            real_eq (real_list_sum Tok0 (fun s' : Tok0 => K s s') states) real_one)
         (Kpos : forall s s' : Tok0, real_lt real_zero (K s s'))
         (keep : Tok0 -> bool)
         (keep_nonempty : sigT (fun s : Tok0 => And (Id (keep s) true) (InT s states)))
         (c : Real)
         (Hrow : forall s : Tok0,
            real_le (tv_row Tok0 states K Kpos keep keep_nonempty s) c)
         (n : nat) (mu : Tok0 -> Real),
    real_eq (real_list_sum Tok0 mu states) real_one ->
    (forall s : Tok0, real_le real_zero (mu s)) ->
    real_le_b (Ddist Tok0 states
                 (kev_iter Tok0 states K Kpos keep keep_nonempty n mu)
                 (k_iter Tok0 states K n mu))
              (real_mult (real_of_nat n) c).
Proof.
  intros Tok0 states Hne K HKnorm Kpos keep keep_nonempty c Hrow n mu Hnorm Hnn.
  apply real_le_closure_b_one. intros eps Heps.
  exact (kv_drift_bound Tok0 states Hne K HKnorm Kpos keep keep_nonempty c Hrow
           n mu eps Hnorm Hnn Heps).
Qed.

(* T3：le_b 乘法因子合成器族（UpReqPowMonoBridge x3d_ 系）补缺面——           *)
(*   常数对直引形（B14 直引形：c 取常数一，正性证书 real_lt_zero_one 直喂     *)
(*   x3d_le_b_mult_r_pos@:192）＋任意非负 Or 形因子直引形（x3d_le_b_mult_r_   *)
(*   nonneg_or@:146 同参重申）。                                              *)
(*   诚实注记：「纯 B 形无上界版」构造性不可通——UpReqPowMonoBridge 件4 自书   *)
(*   B 形非负⟹Or 形反向构造性不通，因子无上界 M 时余量乘出无法压回 eps；      *)
(*   有界版 x3d_le_b_mult_r_nonneg_bnd@:215 在库。真墙域如实登记，非欠账。    *)
Theorem p2t1_x3d_le_b_mult_one : forall a b : Real,
  real_le_b a b -> real_le_b (real_mult a real_one) (real_mult b real_one).
Proof.
  intros a b H.
  exact (x3d_le_b_mult_r_pos a b real_one H real_lt_zero_one).
Qed.

Theorem p2t1_x3d_le_b_mult_r : forall a b c : Real,
  real_le_b a b -> real_le real_zero c ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c H Hc.
  exact (x3d_le_b_mult_r_nonneg_or a b c H Hc).
Qed.

(* T2 挂账注记：UpRealLeB 结论 9(e)/(f) 复合/多 eps 形升格面——源件面实测      *)
(*   real_abs_le_quad_eps@S08:4901 五前件＋四分支内件链（real_abs_le_quad_ll/ *)
(*   _le 等），UpRealLeB 尾注 :760-767 自书「可升格但证书链长且语句须前提位   *)
(*   改造——未建（非冻结，留后续席）」；结论 10 的 16+2 件 plain-eps 面已由    *)
(*   Part E 席升格落盘（禁重做）。本席不虚报 T 级，如实挂账候续席。            *)

(* ################ 段七：Setoid 语境行（置尾节，p1t2 段四体例） ############# *)
(* B27 直引形：req 系 Setoid 语境，常量载体配分和正性。                       *)
(* 行 4：S04:1891/:2012 Z_pos（配分和正性直引）。                            *)
(* 行 5：S06:3854 Z_thermo_pos（注意力侧热力学配分同形）。                    *)

Import RealInterfaceEnhancedMod.

Section P2T1ReqConst.

Context {R0 : Set} {RIS : RealInterfaceEnhancedSetoid R0}.

Theorem p2t1_Z_pos_supply :
  forall (S0 : Set) (sumf : (S0 -> R0) -> R0) (base_loss : S0 -> R0) (D0 : R0),
    (forall f : S0 -> R0, (forall s : S0, lt zero (f s)) -> lt zero (sumf f)) ->
    forall HDpos : lt zero D0,
      lt zero (sumf (fun s : S0 =>
               exp_neg (mult (inv_pos D0 HDpos) (base_loss s)))).
Proof.
  intros S0 sumf base_loss D0 Hfsum HDpos.
  apply Hfsum.
  intro s.
  apply exp_neg_pos.
Qed.

(* 行 5：Z_thermo 形（energy 命名对位 S06:3854 boltzmann_factor 展开体） *)
Theorem p2t1_Z_thermo_pos_supply :
  forall (S0 : Set) (sumf : (S0 -> R0) -> R0) (energy : S0 -> R0) (D0 : R0),
    (forall f : S0 -> R0, (forall s : S0, lt zero (f s)) -> lt zero (sumf f)) ->
    forall HDpos : lt zero D0,
      lt zero (sumf (fun s : S0 =>
               exp_neg (mult (inv_pos D0 HDpos) (energy s)))).
Proof.
  intros S0 sumf energy D0 Hfsum HDpos.
  exact (p2t1_Z_pos_supply S0 sumf energy D0 Hfsum HDpos).
Qed.

(* 行 23：inv_pos_lt_compat（S04:3341 实形）——接口面不可构造， *)
(*   显式前件收拢槽实形（p1t2 B12 打包同形；req 系同名字段镜像） *)
Theorem p2t1_inv_pos_lt_compat_pack :
  forall (a b : R0) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha) ->
    lt (inv_pos b Hb) (inv_pos a Ha).
Proof. intros a b Ha Hb Hlt Hit. exact Hit. Qed.

End P2T1ReqConst.

(* ################ 收尾：G3 提取探针（一人一目录）＋PA 自检 ################ *)
(* 提取见证面取 Q 层纯函数（零 Real 实例闭包依赖，T2 卡魔数区位规避） *)
Definition p2t1_g3_pick (n : nat) : Q :=
  (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp2t1_g3out".
Extraction "p2t1_G3_Cert.ml" p2t1_g3_pick.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions p2t1_pos_const_core.
Print Assumptions p2t1_le_one_const_core.
Print Assumptions p2t1_one_pos_lt.
Print Assumptions p2t1_one_le_one.
Print Assumptions p2t1_T_pos_supply.
Print Assumptions p2t1_T_supply.
Print Assumptions p2t1_D_pos_supply.
Print Assumptions p2t1_Delta_pos_supply.
Print Assumptions p2t1_temp_pos_supply.
Print Assumptions p2t1_min_p_pos_supply.
Print Assumptions p2t1_temperature_pos_supply.
Print Assumptions p2t1_q_pos_supply.
Print Assumptions p2t1_min_p_lt_one_supply.
Print Assumptions p2t1_lt_minus_nonneg_supply.
Print Assumptions p2t1_spp_supply.
Print Assumptions p2t1_evicted_partition_pos_supply.
Print Assumptions p2t1_topk_kept_partition_pos_supply.
Print Assumptions p2t1_vocab_nonempty_supply.
Print Assumptions p2t1_S_finite_cover_supply.
Print Assumptions p2t1_K_leb_true.
Print Assumptions p2t1_K_of_nat_pos.
Print Assumptions p2t1_default_token_witness.
Print Assumptions p2t1_Z_pos_supply.
Print Assumptions p2t1_Z_thermo_pos_supply.
Print Assumptions p2t1_inv_pos_lt_compat_pack.
Print Assumptions p2t1_q_norm_pack.
Print Assumptions p2t1_topk_pickmax_head_pack.
Print Assumptions p2t1_Hrow_pack.
Print Assumptions p2t1_Z_temp_pos_supply.
Print Assumptions p2t1_real_minp_temp_sum_pos_pack.
Print Assumptions p2t1_kv_drift_bound_B.
Print Assumptions p2t1_x3d_le_b_mult_one.
Print Assumptions p2t1_x3d_le_b_mult_r.
