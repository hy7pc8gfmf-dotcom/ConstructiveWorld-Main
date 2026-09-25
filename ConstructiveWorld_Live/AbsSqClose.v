(* ================================================================== *)
(*  AbsSqClose.v —— 绝对值不等式族与配分函数定义钉扎                    *)
(*  使命: 绝对值基本不等式族——asc_abs_lower_pos（|a|<c ⟹ 0<c+a）、       *)
(*        asc_abs_le_intro（|u|≤w 引入律）、asc_sq_nonneg（0≤t²）、       *)
(*        asc_sq_le_abs_sq（t²≤|t|²）、asc_nsq_square_nonneg、            *)
(*        asc_abs_nonneg、asc_abs_sum_le_r（有限和三角不等式），及         *)
(*        配分函数定义钉扎组 czd12_fep_partition/czd12_fep_Z_pos          *)
(*        （Z 取具体有限和 sumd_sumf；正性经头非空列表归纳＋exp_neg_pos）。*)
(*  依赖: S01_BaseRing、fa53_compat_abs、TempSoftmaxInstantiation、       *)
(*        UpReqSumD、S07_RealSetoidExpLog；Stdlib List                    *)
(*  对标: UpReqLogRDF（lrdf_abs_lower_pos/lrdf_abs_le_intro/              *)
(*        lrdf_sq_nonneg/lrdf_sq_le_abs_sq）、UpReqSqrtF                  *)
(*        （nsq_square_nonneg）、UpReqAttnIter（abs_nonneg_h）、           *)
(*        UpReqAttnGibbs（abs_sum_le_r）、UpReqLogCompD（fep_partition）。 *)
(*  构造性: 全件 Qed 闭合、零承认语句；语句面全 Set 层、零 Prop 泄露；      *)
(*        czd12_fep_Z_pos 前提取 Id 形非 nil，归纳件零空支匹配。           *)
(*  编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树     *)
(*        同世界重编），COQLIB/ROCQLIB 全字面环境前缀。                    *)
(* ================================================================== *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.
Require Import TempSoftmaxInstantiation.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* 主节：S01 载体 + DO 可判定序强化（fa53 同款双 Context）        *)
(* ============================================================ *)
Section AbsSqCloseMain.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* fa53 投影别名定式：类字段名 lt_dec 被 Stdlib Compare_dec 遮蔽 *)
Definition asc_lt_dec_id :
  forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ _ lt_d _ _ _ => lt_d
  end.

(* ---- 小件①：−0 == 0（plus_inv_unique 两侧右逆同一） ---- *)
Lemma asc_opp_zero_id : Id (opp zero) zero.
Proof.
  exact (plus_inv_unique zero (opp zero) zero
           (plus_opp zero) (plus_zero zero)).
Qed.

(* ---- 小件②：opp 对合 −−a == a（plus_inv_unique 左侧对齐） ---- *)
Lemma asc_opp_opp : forall a : R, Id (opp (opp a)) a.
Proof.
  intro a.
  exact (plus_inv_unique (opp a) (opp (opp a)) a
           (plus_opp (opp a))
           (id_trans (id_sym (plus_comm a (opp a))) (plus_opp a))).
Qed.

(* ---- 小件③：(−t)² == t² 环小件（#43 环腿；opp_mult_l/r 拼装） ---- *)
Lemma asc_sq_opp : forall t : R, Id (mult t t) (mult (opp t) (opp t)).
Proof.
  intro t.
  exact (id_sym (id_trans (opp_mult_r t (opp t))
                  (id_trans (id_cong opp (opp_mult_l t t))
                            (asc_opp_opp (mult t t))))).
Qed.

(* ---- 小件④（本件新数学点·abs_neg 桥）：a < 0 ⟹ |a| == −a ----
   a<0 ⟹ −a>0（opp_lt_compat + −0==0 变形）⟹ abs_pos 反号支，
   再经 abs_opp 字段回转到 |a|；与 fa53 件3（a≥0 支）合成
   abs 恒等双向桥。 *)
Lemma asc_abs_neg_id : forall a : R, lt a zero -> Id (abs a) (opp a).
Proof.
  intros a Ha.
  exact (id_trans (id_sym (abs_opp a))
                  (abs_pos (opp a)
                     (lt_id_l zero (opp zero) (opp a)
                        (id_sym asc_opp_zero_id) (opp_lt_compat a zero Ha)))).
Qed.

(* ---- #40：|a| < c ⟹ 0 < c + a（real_abs_lt_lower req 槽形） ----
   三分 0? a：正支 |a|==a 双正相加；零支 |0|==0 归 c；负支
   |a|==−a 桥 + fa53 单侧严格平移件。 *)
Theorem asc_abs_lower_pos : forall a c : R, lt (abs a) c -> lt zero (plus c a).
Proof.
  intros a c H.
  destruct (asc_lt_dec_id zero a) as [H0a | [H0eq | Halt]].
  - (* 0 < a：|a|==a，c > a > 0 ⟹ plus_positive *)
    assert (Hc : lt zero c).
    { exact (lt_trans zero a c H0a
               (lt_id_l a (abs a) c (id_sym (abs_pos a H0a)) H)). }
    exact (plus_positive c a Hc H0a).
  - (* 0 == a：c > |0| == 0；c + a 归 c *)
    assert (Hc : lt zero c).
    { exact (lt_id_l zero (abs a) c
               (id_sym (id_trans (id_cong abs (id_sym H0eq)) abs_zero)) H). }
    exact (lt_id_r zero c (plus c a)
             (id_sym (id_trans (id_cong (fun w => plus c w) (id_sym H0eq))
                               (plus_zero c)))
             Hc).
  - (* a < 0：|a|==−a 桥 + fa53 单侧严格平移 *)
    exact (lt_id_l zero (plus (opp a) a) (plus c a)
             (id_sym (id_trans (id_sym (plus_comm a (opp a))) (plus_opp a)))
             (fa53_lt_plus_translate_r (opp a) c a
                (lt_id_l (opp a) (abs a) c
                   (id_sym (asc_abs_neg_id a Halt)) H))).
Qed.

(* ---- #41：u ≤ w ∧ −u ≤ w ⟹ |u| ≤ w（abs_le 引入律槽形） ----
   三分 0? u：正支 |u|==u 直给；零支 |u|==0==u 归一；负支
   |u|==−u 桥变形第二前提。 *)
Theorem asc_abs_le_intro :
  forall u w : R, le u w -> le (opp u) w -> le (abs u) w.
Proof.
  intros u w Huw Hou.
  destruct (asc_lt_dec_id zero u) as [H0u | [H0eq | Hult]].
  - (* 0 < u：|u|==u *)
    exact (le_id_l (abs u) u w (abs_pos u H0u) Huw).
  - (* 0 == u：|u| == |0| == 0 == u 归一 *)
    exact (le_id_l (abs u) u w
             (id_trans (id_trans (id_cong abs (id_sym H0eq)) abs_zero)
                       H0eq)
             Huw).
  - (* u < 0：|u|==−u 桥变形 *)
    exact (le_id_l (abs u) (opp u) w (asc_abs_neg_id u Hult) Hou).
Qed.

(* ---- #42：0 ≤ t²（Qsquare_nonneg 逐点事实槽形） ----
   三分 0? t：正支零乘链 le_mult_compat_weak；零支平方归零；
   负支 (−t)²==t² 环小件变形归正支。 *)
Theorem asc_sq_nonneg : forall t : R, le zero (mult t t).
Proof.
  intro t.
  destruct (asc_lt_dec_id zero t) as [H0t | [H0eq | Htl]].
  - (* 0 < t：0·t == 0 链 + 双 le zero t 弱乘单调 *)
    assert (Hge : le zero t) by (exact (lt_le_iff zero t (inl H0t))).
    exact (le_id_l zero (mult zero t) (mult t t)
             (id_sym (id_trans (mult_comm zero t) (mult_zero t)))
             (le_mult_compat_weak zero t t Hge Hge)).
  - (* 0 == t：t² == 0² == 0 *)
    assert (Htz : Id (mult t t) zero).
    { exact (id_trans (id_cong (fun w => mult w t) (id_sym H0eq))
                      (id_trans (mult_comm zero t) (mult_zero t))). }
    exact (le_id_r zero zero (mult t t) (id_sym Htz) (le_refl zero)).
  - (* t < 0：−t > 0 支 + (−t)²==t² 变形 *)
    assert (Ht0 : lt zero (opp t)).
    { exact (lt_id_l zero (opp zero) (opp t) (id_sym asc_opp_zero_id)
               (opp_lt_compat t zero Htl)). }
    exact (le_id_r zero (mult (opp t) (opp t)) (mult t t)
             (id_sym (asc_sq_opp t))
             (le_id_l zero (mult zero (opp t)) (mult (opp t) (opp t))
                (id_sym (id_trans (mult_comm zero (opp t))
                                  (mult_zero (opp t))))
                (le_mult_compat_weak zero (opp t) (opp t)
                   (lt_le_iff zero (opp t) (inl Ht0))
                   (lt_le_iff zero (opp t) (inl Ht0))))).
Qed.

(* ---- #43：t² ≤ |t|²（q_sq_abs 槽形） ----
   三分 0? t：非负支 |t|==t（fa53 件3 覆盖 lt/eq 双腿）目标即
   le_refl 变形；负支 |t|==−t 桥 + (−t)²==t² 小件串联变形。 *)
Theorem asc_sq_le_abs_sq :
  forall t : R, le (mult t t) (mult (abs t) (abs t)).
Proof.
  intro t.
  destruct (asc_lt_dec_id zero t) as [H0t | [H0eq | Htl]].
  - (* 0 < t：|t|==t *)
    exact (le_id_r (mult t t) (mult t t) (mult (abs t) (abs t))
             (id_sym (id_cong2 mult (abs_pos t H0t) (abs_pos t H0t)))
             (le_refl (mult t t))).
  - (* 0 == t：|t|==0==t 归一 *)
    assert (Haid : Id (abs t) t).
    { exact (id_trans (id_trans (id_cong abs (id_sym H0eq)) abs_zero)
                      H0eq). }
    exact (le_id_r (mult t t) (mult t t) (mult (abs t) (abs t))
             (id_sym (id_cong2 mult Haid Haid)) (le_refl (mult t t))).
  - (* t < 0：|t|==−t 桥 + (−t)²==t² 串联 *)
    assert (Haid : Id (abs t) (opp t)) by (exact (asc_abs_neg_id t Htl)).
    exact (le_id_r (mult t t) (mult t t) (mult (abs t) (abs t))
             (id_sym (id_trans (id_cong2 mult Haid Haid)
                               (id_sym (asc_sq_opp t))))
             (le_refl (mult t t))).
Qed.

(* ---- #44：nsq 位（与 #42 语句逐字同形；核对用独立成件） ---- *)
Theorem asc_nsq_square_nonneg : forall t : R, le zero (mult t t).
Proof.
  exact asc_sq_nonneg.
Qed.

(* ---- #45：0 ≤ |a|（abs 非负平形槽） ----
   正支 |a|==a 升 le；零支 |a|==0 反射；负支 |a|==−a 桥 +
   −a>0 升 le。 *)
Theorem asc_abs_nonneg : forall a : R, le zero (abs a).
Proof.
  intro a.
  destruct (asc_lt_dec_id zero a) as [H0a | [H0eq | Halt]].
  - (* 0 < a：|a|==a 升 le *)
    exact (le_id_r zero a (abs a) (id_sym (abs_pos a H0a))
             (lt_le_iff zero a (inl H0a))).
  - (* 0 == a：|a| == |0| == 0 *)
    assert (Haz : Id (abs a) zero).
    { exact (id_trans (id_cong abs (id_sym H0eq)) abs_zero). }
    exact (le_id_r zero zero (abs a) (id_sym Haz) (le_refl zero)).
  - (* a < 0：|a|==−a 桥 + −a>0 升 le *)
    assert (Ht0 : lt zero (opp a)).
    { exact (lt_id_l zero (opp zero) (opp a) (id_sym asc_opp_zero_id)
               (opp_lt_compat a zero Halt)). }
    exact (le_id_r zero (opp a) (abs a) (id_sym (asc_abs_neg_id a Halt))
             (lt_le_iff zero (opp a) (inl Ht0))).
Qed.

(*
   宿主槽为抽象 sumf 位（无消解/归纳数据，类字段 rabs_sum_le
   同形但为假设位）；S01 接口自带 abs_triangle 平形字段
   （S01:284；RIS 面仅 eps 形），故在 sumd 具体有限和层
   （G1 钥匙 UpReqSumD；RIS 结构经 tsi 桥 = S01 同名投影）
   列表归纳完成证明——特化层为完整定理，抽象层槽保持一般陈述。 *)
Lemma asc_sumd_list_abs_triangle :
  forall (S : Set) (f : S -> R) (l : list S),
    le (abs (sumd_list_sum S f l))
       (sumd_list_sum S (fun s : S => abs (f s)) l).
Proof.
  intros S f l. induction l as [| x t IH].
  - (* nil：|0| == 0 ≤ 0 *)
    exact (le_id_l (abs (sumd_list_sum S f nil)) zero zero
             abs_zero (le_refl zero)).
  - (* cons：abs_triangle + le_plus_compat 双腿（逐项 abs 恒等反射） *)
    exact (le_trans (abs (plus (f x) (sumd_list_sum S f t)))
             (plus (abs (f x)) (abs (sumd_list_sum S f t)))
             (plus (abs (f x)) (sumd_list_sum S (fun s => abs (f s)) t))
             (abs_triangle (f x) (sumd_list_sum S f t))
             (le_plus_compat (abs (f x)) (abs (f x))
                (abs (sumd_list_sum S f t))
                (sumd_list_sum S (fun s => abs (f s)) t)
                (le_refl (abs (f x))) IH)).
Qed.

(* #46 槽形出口（sumd_sumf 特化形） *)
Theorem asc_abs_sum_le_r :
  forall (S : Set) (enum : list S) (f : S -> R),
    le (abs (sumd_sumf S enum f))
       (sumd_sumf S enum (fun s : S => abs (f s))).
Proof.
  intros S enum f. exact (asc_sumd_list_abs_triangle S f enum).
Qed.

End AbsSqCloseMain.

(* ============================================================ *)
(* 尾节：#47 配分函数定义钉扎伴随件（RIS 世界）                   *)
(*   先例：消融50/fa51_sumpos_id.v:158 fa51_Z_temp_spec_def、     *)
(*   G12_ZPosFam zposd_Z（Z 由 Variable 改 Definition 钉扎法）。   *)
(* ============================================================ *)
Require S07_RealSetoidExpLog.
Import S07_RealSetoidExpLog.RealInterfaceEnhancedMod.

Section FepPartitionPin.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.

(* #47 定义钉扎：Z 取具体有限和（sumd_sumf；配分函数 Boltzmann 形） *)
Definition czd12_fep_Z : R :=
  sumd_sumf S enum
    (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s))).

(* partition 槽定义性闭：钉扎后槽语句即 req_refl（fa51 同型先例） *)
Theorem czd12_fep_partition :
  req czd12_fep_Z
      (sumd_sumf S enum
         (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
Proof.
  exact (req_refl czd12_fep_Z).
Qed.

(* 引擎件：头非空列表和逐项正 ⟹ 和正（构造性归纳，零空支匹配：
   非空性由 (x :: l) 头形构造性携带，规避 impossible 支）。 *)
Lemma czd12_list_sum_pos_cons :
  forall (f : S -> R) (x : S) (l : list S),
    (forall s : S, lt zero (f s)) -> lt zero (sumd_list_sum S f (x :: l)).
Proof.
  intros f x l H. revert x. induction l as [| y t IH]; intro x.
  - (* x::nil：和 = f x + 0 归 f x *)
    exact (lt_id_r zero (f x) (plus (f x) (sumd_list_sum S f nil))
             (req_sym (plus (f x) zero) (f x) (plus_zero (f x))) (H x)).
  - (* x::y::t：双正相加 *)
    exact (plus_positive (f x) (sumd_list_sum S f (y :: t))
             (H x) (IH y)).
Qed.

(* #47 Z_pos：sumd 正性 + exp_neg_pos 逐项正（fa51_Z_temp_pos 同型；
   前提取 fa51 同款 Id 形非空证据，Set 层零 Prop）。 *)
Theorem czd12_fep_Z_pos :
  Not (Id enum nil) -> lt zero czd12_fep_Z.
Proof.
  intro Hne. unfold czd12_fep_Z. destruct enum as [| x l].
  - destruct (Hne (@id_refl (list S) nil)).
  - exact (czd12_list_sum_pos_cons
             (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))
             x l
             (fun s : S => exp_neg_pos
                 (mult (inv_pos D D_pos) (base_loss s)))).
Qed.

End FepPartitionPin.

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明） ---- *)
Print Assumptions asc_opp_zero_id.
Print Assumptions asc_opp_opp.
Print Assumptions asc_sq_opp.
Print Assumptions asc_abs_neg_id.
Print Assumptions asc_abs_lower_pos.
Print Assumptions asc_abs_le_intro.
Print Assumptions asc_sq_nonneg.
Print Assumptions asc_sq_le_abs_sq.
Print Assumptions asc_nsq_square_nonneg.
Print Assumptions asc_abs_nonneg.
Print Assumptions asc_abs_sum_le_r.
Print Assumptions czd12_fep_partition.
Print Assumptions czd12_fep_Z_pos.
