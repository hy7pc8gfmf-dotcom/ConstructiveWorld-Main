(* ============================================================ *)
(* UpAblP1T1_AlignCert.v —— 假设消融战役 T1R 席（T1 前席并发墙击坠重发）        *)
(*   论文1 T 批·S05 对齐证书簇 6 束·T 级合并申报件（新独立批件）                  *)
(* 母本：S05_AlignmentGRPO.v（原树零改，只读消费；行号 20260919 现档实测）        *)
(*                                                              *)
(* 辖区六束（普查 _tp1a_ B1/B2/B3/B5/B6/B7 行＋合并单 _tp1m_ T 批节）：          *)
(*   B3 beta_pos       S05:45   lt zero beta        （迭代节 :4595 同形）        *)
(*   B2 positive_dist  S05:47   forall s, lt zero (pi_ref s)（:4597 同形）       *)
(*   B1 normalized     S05:48   Id (sum_over_S pi_ref) one                          *)
(*                     （pi_old_norm :785 同形位，本件供给形同槽覆盖）               *)
(*   B5 eta            S05:2530 数据位               （:4599 同形）               *)
(*   B6 eta_pos        S05:2531 lt zero eta          （:4600 同形）               *)
(*   B7 eta_le_one     S05:2532 le eta one           （:4601 同形）               *)
(*                                                              *)
(* 供给形态（AB1 Hsum_pos 打包形先例＋既有 T 批件体例；T 级＝仅平凡供给，          *)
(* 合并申报不充非平凡战果；显式 forall 前件供给件）：                              *)
(*   B3：p1t1_beta_pos_supply——任意正有理常数 q 给 beta := real_const q 的       *)
(*       Real 载体正性证书（real_lt 逐点展开，eps := q/2，照 S07                  *)
(*       real_lt_zero_one 先例；Q 层乘法保序走全参显式项，防隐元乱配）；           *)
(*   B1/B2：T13c 单点 SumOver 实例世界（uab_ssUnit+uab_soUnit，全库唯一具体       *)
(*       SumOver 实例，UpAblT13c_G13.v:41/:71）上常值一核 supply——                *)
(*       B2 由 one_pos 接口字段直喂（apply 形，基类投影面），                      *)
(*       B1 由单点和退化 f 核元素＋one 本身、exp_neg_zero 通路 id_refl 闭；        *)
(*       两件对抽象载体全参（forall RI0），零具体实例依赖；                        *)
(*   B5/B6/B7：eta 取 (0,1) 内有理见证族 p1t1_eta_family q := real_const q——      *)
(*       正性与 B3 共享（束间 Shared Context 减重复）；≤一 走 real_lt 展开        *)
(*       ＋Qmult_lt_compat_r 全参项；改写面出现位定向（at 2）绕 Qminus 与          *)
(*       Qplus 的增量展开同形穿透坑；端点 eta := one 由 real_lt_zero_one          *)
(*       （B6 端点）与 real_le_refl（B7 端点）双供；                              *)
(*       B5 本体＝见证族＋sigT 打包供给 p1t1_eta_supply（AB1 sigT 打包形）。       *)
(* 防重认领（20260919 实测）：UpAblT5_S05_AlignmentGRPO.v 辖区＝                  *)
(*   inv_pos_lt_contra/log_lt_mono，与本六束零重叠（grep 实测）；N-1/N-2           *)
(*   （Z_align_pos/sum_over_S_pos，S05:54/4598/2535/4602）禁区未碰；               *)
(*   B10-B18 各槽另席另批，本件不越界。                                            *)
(* 纪律：纯构造性零承认件／语句面全 Set 层（Id/sigT/And/Or 别名面，裸命题         *)
(*   零入语句与前提位）／公理面零新增／原树零改／前缀 p1t1_ 防撞；                 *)
(*   不入 order.txt/_CoqProject；禁触 9.0 任何产物。                               *)
(* 四关留痕：attn/logs/g{1..4}-UpAblP1T1_AlignCert.log；G3 提取一人一目录          *)
(*   _tp1t1_g3out（验后判读）。                                                    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpAblT13c_G13.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Extraction.

(* ################ B3：beta_pos 供给（任意正有理常数构造） ################ *)
(* 槽形：S05:45 lt zero beta（beta 为数据位）。供给引理给出 Real 载体证书：      *)
(* 任取正有理 q，beta := real_const q 满足正性槽形。                             *)
Theorem p1t1_beta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
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

(* ################ B1：normalized 供给（单点世界常值一核） ################ *)
(* 槽形：S05:48 Id (sum_over_S pi_ref) one（:785 pi_old_norm 同形）。            *)
(* T13c 单点 SumOver 实例世界：和退化为核元素取值，常值一核求和即 one。          *)
Theorem p1t1_pi_ref_norm_supply : forall RI0 : RealInterfaceEnhanced,
  Id (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
        (fun _ : @S RI0 (@uab_ssUnit (@RI_base RI0)) => @one RI0)) (@one RI0).
Proof. intros RI0. exact id_refl. Qed.

(* ################ B2：positive_dist 供给（常值一核逐点正） ################ *)
(* 槽形：S05:47 forall s, lt zero (pi_ref s)。one_pos 接口字段直喂。             *)
Theorem p1t1_pi_ref_pos_supply : forall (RI0 : RealInterfaceEnhanced)
    (s : @S RI0 (@uab_ssUnit (@RI_base RI0))),
  @lt RI0 (@zero RI0)
    ((fun _ : @S RI0 (@uab_ssUnit (@RI_base RI0)) => @one RI0) s).
Proof. intros RI0 s. apply (@one_pos RI0). Qed.

(* ################ B5/B6/B7 共享面：eta 见证族（(0,1) 内有理族） ############ *)
Definition p1t1_eta_family (q : Q) : Real := real_const q.

(* ################ B6：eta_pos 供给（见证族正性，与 B3 共享） ################ *)
Theorem p1t1_eta_pos_supply : forall q : Q, QltT (0#1)%Q q ->
  real_lt real_zero (p1t1_eta_family q).
Proof. intros q Hq. exact (p1t1_beta_pos_supply q Hq). Qed.

(* ################ B7：eta_le_one 供给（见证族 ≤ 一） ###################### *)
Theorem p1t1_eta_le_one_supply : forall q : Q, QltT q (1#1)%Q ->
  real_le (p1t1_eta_family q) real_one.
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

(* ################ B5：eta 数据位供给（sigT 打包：见证族给付） ############## *)
(* 槽形：S05:2530 eta : 数据位。打包形给 (0,1) 内任取 q 的具证 eta 见证。        *)
Theorem p1t1_eta_supply : forall q : Q, QltT (0#1)%Q q -> QltT q (1#1)%Q ->
  sigT (fun e : Real => And (real_lt real_zero e) (real_le e real_one)).
Proof.
  intros q Hq0 Hq1.
  exact (existT (fun e : Real => And (real_lt real_zero e) (real_le e real_one))
                (p1t1_eta_family q)
                ((p1t1_eta_pos_supply q Hq0), (p1t1_eta_le_one_supply q Hq1))).
Qed.

(* #### 端点补全：eta := one（(0,1] 的右端点，B6/B7 端点各一直喂） ########## *)
Theorem p1t1_eta_one_pos : real_lt real_zero real_one.
Proof. exact real_lt_zero_one. Qed.

Theorem p1t1_eta_one_le_one : real_le real_one real_one.
Proof. exact (real_le_refl real_one). Qed.

(* ---- G3 提取探针（一人一目录 _tp1t1_g3out；验后判读 Obj.magic 计数） ----- *)
Definition p1t1_eta_pick (n : nat) : Q := (1 # (Pos.succ (Pos.succ (Pos.of_succ_nat n))))%Q.

Set Extraction Output Directory "_tp1t1_g3out".
Extraction "p1t1_G3_AlignCert.ml" p1t1_eta_pick.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions p1t1_beta_pos_supply.
Print Assumptions p1t1_pi_ref_norm_supply.
Print Assumptions p1t1_pi_ref_pos_supply.
Print Assumptions p1t1_eta_pos_supply.
Print Assumptions p1t1_eta_le_one_supply.
Print Assumptions p1t1_eta_supply.
Print Assumptions p1t1_eta_one_pos.
Print Assumptions p1t1_eta_one_le_one.
