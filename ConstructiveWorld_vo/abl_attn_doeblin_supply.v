(* ==========================================================================)
   abl_attn_doeblin_supply.v — AT1 AttnDoeblin 试点席（第五批·非冻结最优起点
   外置供给件：Doeblin 收缩数据槽见证与平滑核构造族，计 8 供给定理）
   ── 使命：基座区覆盖图 AttnDoeblin 行（order L16，37 槽＝构7/绿2/黄14/白14）
      试点供给——37 槽逐槽速判四步分拣（步0 层位/步1 形态对表/步2 实例供给/
      步3 双态，全表入交付报告）后，白命题槽 7 全数选中（现档行 :154 u_norm/
      :156 delta_lt_one/:158 transition_nonneg/:159 transition_row/:160
      minorization/:467 z_lb/:468 z_ub），另以构造值伴随覆盖参数位 5（:153 u/
      :155 delta/:157 transition/:466 z/:460 enum），合计选槽 12。供给形分两型：
      A 直供见证形（sigT 装箱：② delta one 实例见证／① 均匀分布归一见证／⑥
      零带 z 见证）与 B 全参喂形（③④⑤ 平滑核三证书——非负/行随机/次要化对
      构造核成立；⑧ 旗件以构造核喂入 u_tv_contraction 得 1−δ 收缩，minorization
      槽在前提面消除；⑦ Part A 接口数据总见证，对标件内 real_expf_realizable
      之 Part C 角色）。temp(:462)/expf(:471) 两参数位不施工；:161/:165 两黄槽
      与 :472-476 expf 五槽等黄面邻接坐标登记不重复供给（uabl_attn_full_instance
      十九字段实例面在役已覆盖，零重复立项）。
   ── 依赖：S01_BaseRing 至 S15_TailFEPUp 基座链＋AttnDoeblin（全部只读引用，
      原件零字节不动、零级联；本件实消费 AttnDoeblin 导出面 nat_to_R/
      nat_to_R_pos/delta_absorb_u/u_tv_contraction 四名，Require 非名义性）。
   ── 对标行：供给句式＝沙箱/现役/abl_tail_supply_pool/_log/供给件配方笔记
      -20260930.md §2.1/§2.2；见证形先例＝tspb_ems_sum_pos_preserved_witness@
      abl_tail_sum_pos_bridge.v:122（generic S/en sigT 非空形）＋
      tspu_p7b3_enum_nonempty@abl_tail_slot_upgrade.v:149（cons 形非空闭形）；
      one 实例证书先例＝tspp 系@abl_tail_pos_certs.v:131-224；总见证先例＝
      real_expf_realizable@AttnDoeblin.v:771（sigT 五字段）；零带 z 先例＝
      tspy_p7d_z_lb_zero@abl_tail_deep_slots.v:131（one 钉定形，本件泛 Delta
      形强之）；平滑核代数链同构＝AttnDoeblin.v:171-192（u_omd_pos_next/
      u_r_nonneg）；出节全参签名机读＝本池 _log/probe_abla_attn-20261001.log
      （u_tv_contraction 十一参 discharge 序，transition_nonneg 不入其签名）。
   ── 构造性注记：全件零承认式声明、零悬置前提、零经典逻辑；语句面承载位全
      Set 形（Id/le/lt/Or/And/Not 皆 S01 Set 值定义，sigT/And 装箱同
      real_expf_realizable 体例）；平滑核族前提＝u_norm/u_nonneg/delta_nonneg/
      delta_lt_one/transition_nonneg/transition_row 六件，皆为槽族泛形数据义务
      的显式保持（禁硬证，如实申报）；旗件另取 :161/:164/:165 三接口件为显式
      前提位（槽面逐字）；全部结论 Qed 真构造闭合；Print Assumptions 十一名
      全 Closed 判据（名清单=Qed 计数=11 零差）；提取探针 Obj.magic 分段计数
      如实登记（G3 对照实验口径：u_tv_contraction 单独提取＝库层闭包对照臂）。
   ── 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&
      ulimit -s 65532 && cd 本池；道闸核 rocq 进程数 ≤1 后单道执行
      nice -19 rocq c -native-compiler no -Q <统一缓存根> ""
      abl_attn_doeblin_supply.v；绿判四件套：EXIT=0／日志真错行 0／vo 头 8 字节
      436f7121 00015ff4／vo 新于 v；G4 第五证 rocqchk -o 参数=模块名
      abl_attn_doeblin_supply。
   ── 交付声明：本件为中文声明的零承认件：全文件零承认式声明、零悬置前提、
      零经典逻辑，全部结论 Qed 真构造闭合。
   ========================================================================== *)

From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import AttnDoeblin.

(* ============================================================ *)
(* 查重登记块（禁重复供给声明，R1 先例照办）：                        *)
(*   （一）:164 abs_ge_zero_id_cc 与 :482 bs_abs＝ali_abs_ge_zero_id@  *)
(*   AbsLeId.v:42 逐字同形已供（fa53 件3 链），本件零触碰，锚对照入报告。*)
(*   （二）:472-476 expf 五槽＝real_expf_realizable@AttnDoeblin.v:771  *)
(*   在役总见证＋uabl_attn_full_instance.v Part A 实例面已覆盖，零触碰。*)
(*   （三）:479/:482/:483 三接口件与 :461/:463/:465/:492 世界证书位＝  *)
(*   uabl Part B/C 十九字段实例面在役（Fin2），零重复；Id 面条件形＝    *)
(*   uabl Part E（DO 前提随件形态）在役。                              *)
(*   （四）:154/:156/:158/:159/:160/:467/:468 七白命题槽为本件领地，   *)
(*   在役无同语句供给（覆盖图白14 族级初判与本件逐槽现档分拣双登记）。  *)
(* ============================================================ *)

(* ============================================================ *)
(* 区一：delta_lt_one 槽（:156）one 实例见证——步2 实例供给=zero 实例，  *)
(*   one_pos 一击；语句面=sigT 见证形（Set 层，层位红线过）。           *)
(* ============================================================ *)

Section AblaDeltaSlot.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Theorem abla_delta_lt_one_witness : sigT (fun d : R => lt d one).
Proof.
  exact (existT _ zero one_pos).
Qed.

End AblaDeltaSlot.

(* ============================================================ *)
(* 区二：u_norm 槽（:154）均匀分布归一见证——generic S 形（cons 形非空，  *)
(*   tspu_p7b3 配方）；列表和自持重演（abla_list_sum，66 件池规：不消费  *)
(*   件内 Section 局部 Fixpoint，如实双登记）；nat_to_R/nat_to_R_pos 消费 *)
(*   AttnDoeblin 导出面（签名经探针机读钉定）。                         *)
(* ============================================================ *)

Section AblaUnifWitness.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Fixpoint abla_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | x :: t => plus (f x) (abla_list_sum f t)
  end.

Lemma abla_list_sum_const : forall (c : R) (l : list S),
  Id (abla_list_sum (fun _ : S => c) l) (mult (nat_to_R (length l)) c).
Proof.
  intros c l. induction l as [| x t IH].
  - apply (id_sym (id_trans (mult_comm zero c) (mult_zero c))).
  - assert (Hstep : Id (plus c (abla_list_sum (fun _ : S => c) t))
                       (plus (mult c one) (mult c (nat_to_R (length t))))).
    { exact (id_cong2 plus (id_sym (mult_one c))
                           (id_trans IH (mult_comm (nat_to_R (length t)) c))). }
    apply (id_trans Hstep).
    apply (id_trans (id_sym (distrib c one (nat_to_R (length t))))).
    apply (mult_comm c (plus one (nat_to_R (length t)))).
Qed.

(* 供给①：u_norm 槽（:154）见证形——任一非空有限世界（cons 形 enum＋求和
   钉定公理）上，均匀分布 fun _ => 1/|enum| 为归一化分布之构造见证。 *)
Theorem abla_unif_norm_witness :
  forall (x : S) (rest : list S),
    (forall g : S -> R, Id (sum_over_S g) (abla_list_sum g (x :: rest))) ->
    sigT (fun uu : S -> R => Id (sum_over_S uu) one).
Proof.
  intros x rest Hsum_eq.
  assert (HnR : lt zero (nat_to_R (length (x :: rest)))).
  { exact (nat_to_R_pos (length rest)). }
  exists (fun _ : S => inv_pos (nat_to_R (length (x :: rest))) HnR).
  apply (id_trans (Hsum_eq (fun _ : S => inv_pos (nat_to_R (length (x :: rest))) HnR))).
  apply (id_trans (abla_list_sum_const
                    (inv_pos (nat_to_R (length (x :: rest))) HnR) (x :: rest))).
  exact (inv_pos_correct (nat_to_R (length (x :: rest))) HnR).
Qed.

End AblaUnifWitness.

(* ============================================================ *)
(* 区三：transition 三槽（:158/:159/:160）平滑核构造族＋旗件——Doeblin    *)
(*   平滑：T_δ := (1−δ)·T + δ·u。前提六件=泛形数据义务显式保持（含       *)
(*   delta_nonneg 为 δ·u 非负之需，如实申报）；结论=构造核对三槽逐槽成立； *)
(*   旗件以构造核喂入 u_tv_contraction（出节全参，探针机读序），         *)
(*   minorization 槽在旗件前提面消除（B 全参喂形精简版先例 rta_ 系）。   *)
(* ============================================================ *)

Section AblaSmoothFamily.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable u_nonneg : forall s : S, le zero (u s).
Variable delta : R.
Variable delta_nonneg : le zero delta.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s' : S, le zero (transition s s').
Variable transition_row : forall s : S, Id (sum_over_S (fun s' : S => transition s s')) one.
Variable sum_swap_cc : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable abs_ge_zero_id_cc : forall a : R, le zero a -> Id (abs a) a.
Variable lt_plus_compat_lt_le_h : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Let omd := minus one delta.

Definition abla_smooth_kernel (s s' : S) : R :=
  plus (mult omd (transition s s')) (mult delta (u s')).

Lemma abla_omd_nonneg : le zero omd.
Proof.
  exact (le_minus_nonneg delta one (lt_le_iff delta one (inl delta_lt_one))).
Qed.

Lemma abla_delta_plus_omd : Id (plus delta omd) one.
Proof.
  apply (id_trans (id_sym (id_cong2 plus (mult_one delta) (mult_one omd)))
                  (delta_absorb_u delta one)).
Qed.

(* 供给③：transition_nonneg 槽（:158）构造形——平滑核逐点非负。 *)
Theorem abla_smooth_nonneg : forall s s' : S, le zero (abla_smooth_kernel s s').
Proof.
  intros s s'. unfold abla_smooth_kernel.
  apply (le_id_l zero (plus zero zero)
         (plus (mult omd (transition s s')) (mult delta (u s')))
         (id_sym (plus_zero zero))).
  apply (le_plus_compat zero (mult omd (transition s s'))
                        zero (mult delta (u s'))).
  - exact (le_mult_nonneg_t12 omd (transition s s')
             abla_omd_nonneg (transition_nonneg s s')).
  - exact (le_mult_nonneg_t12 delta (u s') delta_nonneg (u_nonneg s')).
Qed.

(* 供给④：transition_row 槽（:159）构造形——平滑核行随机。 *)
Theorem abla_smooth_row :
  forall s : S, Id (sum_over_S (fun s' : S => abla_smooth_kernel s s')) one.
Proof.
  intro s. unfold abla_smooth_kernel.
  apply (id_trans (sum_over_S_add (fun s' : S => mult omd (transition s s'))
                                  (fun s' : S => mult delta (u s')))).
  apply (id_trans (id_cong2 plus
    (id_trans (sum_over_S_linear omd (fun s' : S => transition s s'))
              (id_cong (fun w : R => mult omd w) (transition_row s)))
    (id_trans (sum_over_S_linear delta u)
              (id_cong (fun w : R => mult delta w) u_norm)))).
  apply (id_trans (id_cong2 plus (mult_one omd) (mult_one delta))).
  apply (id_trans (plus_comm omd delta)).
  exact abla_delta_plus_omd.
Qed.

(* 供给⑤：minorization 槽（:160）构造形——δ·u ≤ (1−δ)·T + δ·u。
   槽泛形（任意 transition 上次要化）＝真前提数据义务保持；本件供其
   N3 构造实例路线：平滑核对次要化无条件成立。 *)
Theorem abla_smooth_minorization :
  forall s s' : S, le (mult delta (u s')) (abla_smooth_kernel s s').
Proof.
  intros s s'. unfold abla_smooth_kernel.
  apply (le_id_l (mult delta (u s')) (plus (mult delta (u s')) zero)
         (plus (mult omd (transition s s')) (mult delta (u s')))
         (id_sym (plus_zero (mult delta (u s'))))).
  exact (le_id_l (plus (mult delta (u s')) zero) (plus zero (mult delta (u s')))
                 (plus (mult omd (transition s s')) (mult delta (u s')))
                 (plus_comm (mult delta (u s')) zero)
                 (le_plus_compat zero (mult omd (transition s s'))
                                 (mult delta (u s')) (mult delta (u s'))
                   (le_mult_nonneg_t12 omd (transition s s')
                      abla_omd_nonneg (transition_nonneg s s'))
                   (le_refl (mult delta (u s'))))).
Qed.

(* 供给⑧（旗件）：B 全参喂形——以平滑核实例化 u_tv_contraction，前提面
   不含 minorization（由供给⑤喂入）；u_norm/delta_lt_one 与三接口件保持
   显式前提位。目标件导出面实消费（非名义性 Require）。 *)
Theorem abla_smooth_tv_contraction : forall (mu nu : S -> R),
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  le (tv_dist (@attention_step RI SS SO abla_smooth_kernel mu)
              (@attention_step RI SS SO abla_smooth_kernel nu))
     (mult (minus one delta) (tv_dist mu nu)).
Proof.
  intros mu nu Hmu Hnu.
  exact (@u_tv_contraction RI SS SO u u_norm delta delta_lt_one
           abla_smooth_kernel abla_smooth_row abla_smooth_minorization
           sum_swap_cc abs_ge_zero_id_cc lt_plus_compat_lt_le_h
           mu nu Hmu Hnu).
Qed.

End AblaSmoothFamily.

(* ============================================================ *)
(* 区四：Part A 接口数据总见证——复制核 T(s,s'):=u(s') 下三 transition 槽  *)
(*   同时成立之 sigT 装箱（real_expf_realizable 体例之 Part A 对位件）。 *)
(* ============================================================ *)

Section AblaUconInhabitant.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Variable u : S -> R.
Variable u_norm : Id (sum_over_S u) one.
Variable u_nonneg : forall s : S, le zero (u s).
Variable delta : R.
Variable delta_lt_one : lt delta one.

Theorem abla_ucon_data_realizable :
  sigT (fun T : S -> S -> R =>
    And (forall s s' : S, le zero (T s s'))
        (And (forall s : S, Id (sum_over_S (fun s' : S => T s s')) one)
             (forall s s' : S, le (mult delta (u s')) (T s s')))).
Proof.
  exists (fun (_ s' : S) => u s').
  assert (Hnn : forall s s' : S, le zero (u s')).
  { intros _ s'. exact (u_nonneg s'). }
  assert (Hrow : forall s : S, Id (sum_over_S (fun s' : S => u s')) one).
  { intro s.
    exact (id_trans (sum_over_S_ext (fun s' : S => u s') u
                       (fun s2 : S => id_refl)) u_norm). }
  assert (Hmin : forall s s' : S, le (mult delta (u s')) (u s')).
  { intros _ s'.
    exact (le_trans (mult delta (u s')) (mult (u s') one) (u s')
             (le_id_l (mult delta (u s')) (mult (u s') delta)
                      (mult (u s') one)
                      (mult_comm delta (u s'))
                      (le_mult_compat_r (u s') delta one
                         (u_nonneg s')
                         (lt_le_iff delta one (inl delta_lt_one))))
             (le_id_l (mult (u s') one) (u s') (u s')
                      (mult_one (u s')) (le_refl (u s')))). }
  exact (pair Hnn (pair Hrow Hmin)).
Qed.

End AblaUconInhabitant.

(* ============================================================ *)
(* 区五：z_lb/z_ub 双槽（:467/:468）零带 z 见证——z₀:=fun _ _=>zero 对   *)
(*   任一正 Delta 满足双界（泛 Delta 形，强于 tspy one 钉定形）；        *)
(*   类字段四步：lt_le_iff 左支＋opp_le_compat＋opp_zero_t13＋le_id_r。  *)
(* ============================================================ *)

Section AblaZBand.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

Theorem abla_z_band_zero_witness :
  forall Delta : R, lt zero Delta ->
  sigT (fun z : S -> S -> R =>
    And (forall s s' : S, le (opp Delta) (z s s'))
        (forall s s' : S, le (z s s') Delta)).
Proof.
  intros Delta HDelta.
  exists (fun (_ _ : S) => zero).
  assert (Hlb : forall s s' : S, le (opp Delta) zero).
  { intros _ _.
    exact (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                   (opp_le_compat zero Delta
                      (lt_le_iff zero Delta (inl HDelta)))). }
  assert (Hub : forall s s' : S, le zero Delta).
  { intros _ _. exact (lt_le_iff zero Delta (inl HDelta)). }
  exact (pair Hlb Hub).
Qed.

End AblaZBand.

(* ============================================================ *)
(* 审计段（对照 Check 读面＋逐件 Closed 判读）                           *)
(* ============================================================ *)

Check abla_delta_lt_one_witness.
Check abla_unif_norm_witness.
Check abla_smooth_nonneg.
Check abla_smooth_row.
Check abla_smooth_minorization.
Check abla_smooth_tv_contraction.
Check abla_ucon_data_realizable.
Check abla_z_band_zero_witness.
Check (@u_tv_contraction).
Check (@nat_to_R).
Check (@nat_to_R_pos).
Check (@delta_absorb_u).

(* 前提面审计（逐件全 Closed 判据；名清单=Qed 计数=11 零差） *)
Print Assumptions abla_delta_lt_one_witness.
Print Assumptions abla_list_sum_const.
Print Assumptions abla_unif_norm_witness.
Print Assumptions abla_omd_nonneg.
Print Assumptions abla_delta_plus_omd.
Print Assumptions abla_smooth_nonneg.
Print Assumptions abla_smooth_row.
Print Assumptions abla_smooth_minorization.
Print Assumptions abla_smooth_tv_contraction.
Print Assumptions abla_ucon_data_realizable.
Print Assumptions abla_z_band_zero_witness.

(* ============================================================ *)
(* 提取检验区（判据＝Obj.magic 分段计数如实登记；G3 对照口径：            *)
(*   末条 u_tv_contraction 单独提取＝库层闭包对照臂）                    *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction abla_delta_lt_one_witness abla_unif_norm_witness
  abla_smooth_nonneg abla_smooth_row abla_smooth_minorization
  abla_smooth_tv_contraction abla_ucon_data_realizable
  abla_z_band_zero_witness.
Recursive Extraction u_tv_contraction.
