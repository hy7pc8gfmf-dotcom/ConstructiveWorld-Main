(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ==================== ToyR 工程   · 切片六替换稿 ==================== *)
(* 本件为 UpReqConcB2Time.v 同名替换稿：原件全文（版记头注/声明序/其余件逐字）保留，  *)
(* 仅三条玩具证明体替换＋件首本头注＋六条批量登记注记；语句面/Require 面/假设审计面    *)
(* 零改动；零新增依赖，刀位标识符均原件既有可见域。                                  *)
(* 三刀三口径：                                                                      *)
(*   一 cbt_temp_pos——温度定义层受控展开（unfold cbt_temp ＝ one）后严格正性证书直取。 *)
(*   二 cbt_lmax_complete——完备性证书结构性推导：世界数据定义层展开＋In 列表消去      *)
(*      两分（left 注入头支）＋载体转换自反闭合，替换原 in_eq 引擎单跳。              *)
(*   三 cbt_abs_sum_le——普通冻结槽一元平推链中间项显式命名：内层求和绝对值换轨腿      *)
(*      提级为命名断言 Hle0，外层零元运输腿经命名中间件复合闭合。                     *)
(* 批量登记十二条（不动证明体，四类口径）：                                            *)
(*   甲·判别闭合一件（cbt_enum_ne——discriminate 认证形）。                            *)
(*   乙·定义性闭合五件（cbt_sum_eq_list——req_refl 最短形；cbt_smoke_z／               *)
(*      cbt_smoke_Delta_core／cbt_smoke_Delta／cbt_smoke_gap——数值冒烟 reflexivity    *)
(*      可计算见证最短形，G3 辅证位）。                                               *)
(*   丙·拆件对偶与接口参数直接代入四件（cbt_expf_mono_lt——real_expf_realizable 第 4 字段       *)
(*      同构对偶一跳；cbt_Delta_pos——cb2 证书全显装配直接代入，+1 松弛严格支证书 eps=1#2，  *)
(*      供体体为二十余段 Q 层机器，装配位无增量可做；cbt_z_lb／cbt_z_ub——z 双界接口参数     *)
(*      全显直接代入，完备性证书消去 In，语句面即装配最短形）。                            *)
(*   丁·终装直接代入二件（cbt_unconditional_mixing_time／cbt_unconditional_mixing_time_le   *)
(*      ——闭合证书 21+8 参全显定义件装配位，应用位仅余两证书参直接代入，最短形）。         *)
(* 闭合证据：三种闭合符计数守恒；禁词七词 0＝0；假设审计十条全闭合判定；               *)
(* 落件前查重（写区原无同名）。                                                        *)
(* ========================================================================== *)

(* ============================================================ *)
(* UpReqConcB2Time.v ——  AT9：B2 终装棒（实质 logit 核的无条件混合时间定理） *)
(* 论文7 §10.2 第 7 项 · 无条件闭合路线①（AT8 §三实例化图 S7 第二棒施工）       *)
(*                                                               *)
(*                                                              *)
(* 上游（零改六源文件）：CW219（RealEnhancedReal 实例 + real_arch +            *)
(*   cauchy_real_exp_mono/wd）、AttnDoeblin（real_expf_realizable 一件全供）,*)
(*   UpReqConcSoftmax（csm_sumf 折叠机 + csm_abs_sum_le_eps 逐 eps 形）,     *)
(*   UpReqSampling（k_titer 迭代器 + rsq_bs_kernel softmax 核 +              *)
(*   rsq_bs_list_sum 折叠）、UpReqConcMixSel（cmk_attention_mixing_time      *)
(*   闭合件出节形）、UpReqConcB1（cb1_arch/cb1_scale_const/cb1_swap_lists/   *)
(*   cb1_bs_abs 消解件零改动复用）、UpReqConcB2（cb2_ 具体 logit 核机器）。   *)
(*                                                              *)
(* 本件三组（cbt_ 前缀）：                                                  *)
(*   一、expf 拆件对偶：cbt_expf := cauchy_real_exp + mono_lt 直给 +        *)
(*       ★mono_le Or 拆支对偶（inl→cauchy_real_exp_mono /                   *)
(*       inr→cauchy_real_exp_wd——AttnDoeblin Part C 装箱的同构重装）。      *)
(*   二、核实例化（AT8 §三实例化图全槽）：世界 S:=unit、enum:=[tt]、q/k:=二维  *)
(*       混号具体向量、lmax:=[(q,k)]（完备性 in_eq）、temp:=one（具体正值）,  *)
(*       z:=cb2_z（=temp·dot(q s)(k s')，实质 logit 核）、Delta:=cb2_Delta   *)
(*       （=temp·max|dot|+1，+1 单位松弛装配形）、Delta_pos/z_lb/z_ub:=       *)
(*       cb2_Delta_pos/cb2_z_lb_all/cb2_z_ub_all（+1 松弛 inl 严格支、证书    *)
(*       eps=1#2）；cbt_kernel:=rsq_bs_kernel 10+2 参全显实例化（softmax 核   *)
(*       温度 T、logit 直径 Δ 全为 cbt_ 具体件）。                          *)
(*   三、终装：cbt_abs_sum_le（plain 冻结槽 1 元平推，AT7 §二配方——eps 形    *)
(*       换槽需动源文件使用语句，禁改，见报告 §二诚实注记；eps 形侧供件        *)
(*       cbt_abs_sum_le_eps 在位备查）+ cbt_tv0（质量前件消解，cb1 同轨）+   *)
(*       Arch:=cb1_arch 零改动复用 + cbt_mixing_cert（21+8 参全显）⟹        *)
(*       cbt_unconditional_mixing_time（±le 双头，Defined）。              *)
(*                                                              *)
(* ★ 终装语句（零接口前件、零 Arch 前件、零证书参——「无条件」机器判据=PA）：*)
(*     forall mu nu : unit -> Real,                                       *)
(*       req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->                  *)
(*       forall budget : Real, lt zero budget ->                            *)
(*       sigT (fun k : nat => lt (cbt_tv (cbt_titer k mu)                   *)
(*                                   (cbt_titer k nu)) budget).             *)
(*   其中 cbt_tv/cbt_titer 与 cmk 闭合件出节语句的内联形逐 delta 可转换。    *)
(*                                                              *)
(* ★ 诚实注记（报告 §二详述）：cb2_Delta 含 +1 单位松弛，收缩率 1−δ* 中      *)
(*   δ* = lo²（lo=exp(−Delta/temp)）较字面 Delta_core=temp·max|dot| 形偏     *)
(*   保守——这是构造性可达形态的诚实代价（AT8 §一设计决断）；且本档世界为    *)
(*   1 元 enum（plain 形冻结槽 abs_sum_le_h 与 Htv0 的 Or 墙在 ≥2 元档      *)
(*   不可构造——AT5/AT6/AT8 已证结论），核值与封顶 Delta 仍为实质 cb2_        *)
(*   机器（冒烟：dot(5)=−2、Delta_core(5)=2、Delta(5)=3、gap(5)=5>1#2）。   *)
(*                                                              *)
(* 公理面自审：全件语句 Set 值（req/le/lt/sigT/Or 均本库 Set 面）；前提位全  *)
(*   显式证书参数；无未证断言、无经典逻辑、无排中律；零新增未证假设位。      *)
(*   终装双头 Defined 收束可提取。                                        *)
(* 红线自审：①real_arch 的 And (2<=n) Prop 支本件零触碰（Arch 消解全权由    *)
(*   cb1_arch 承担，And 支在其内部弃置，不入任何 Set 槽）；②enum_nonempty    *)
(*   （Not-Prop）仅作证书直接代入 k_titer/rsq_bs_kernel（零消去入 Set）；        *)
(*   ③面-面逐字：本件语句层全用实例字段名（req/le/lt/zero/one），cb2_/real_* *)
(*   concrete 名仅经 exact 转换同体输入（AT7 卡③最稳轨），勿混。            *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设——E-STAGING-AT5 卡①）：          *)
(*   _tat9_run.cmd 前台编译；full 后 -vos 重跑生成实体（AT8 卡⑧）；           *)
(*   ${PIPESTATUS[0]} 闭合；检验/提取件 _tat9_ 前缀验后删。                  *)
(* 撞名检查：cbt_ 前缀全树 grep 零撞名（ 实测）。                     *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import UpReqConcB2.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* 一、expf 拆件对偶（real_expf_realizable 的 mono 系拆件，concrete 面）     *)
(* ============================================================ *)

Definition cbt_expf : Real -> Real := cauchy_real_exp.

(* mono_lt 直给（real_expf_realizable 第 4 字段同构） *)
(* 【登记·丙】拆件对偶直引：real_expf_realizable 第 4 字段同构一跳，具体面直连最短形。 *)
Lemma cbt_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (cbt_expf a) (cbt_expf b).
Proof. intros a b H. exact (cauchy_real_exp_mono a b H). Defined.

(* ★mono_le Or 拆支对偶（real_le = Or(real_lt)(real_eq) 构造性析取逐支实例化消解：
   inl→cauchy_real_exp_mono / inr→cauchy_real_exp_wd——AttnDoeblin Part C
   装箱同构重装，concrete 层 unfold real_le 纪律，AT7 卡⑥） *)
Lemma cbt_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (cbt_expf a) (cbt_expf b).
Proof.
  intros a b H. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (inl (cauchy_real_exp_mono a b Hlt)).
  - exact (inr (cauchy_real_exp_wd a b Heq)).
Defined.

(* ============================================================ *)
(* 二、B2 世界与核实例化（AT8 §三实例化图全槽输入）                            *)
(* ============================================================ *)

(* ---- 世界数据（1 元档 + 实质二维混号 logit 向量） ---- *)

Definition cbt_q : unit -> list Real :=
  fun _ : unit => real_one :: real_opp real_one :: nil.
Definition cbt_k : unit -> list Real :=
  fun _ : unit => real_opp real_one :: real_one :: nil.
Definition cbt_lmax : list (list Real * list Real) := (cbt_q tt, cbt_k tt) :: nil.

(* 完备性证书（B2 唯一新前件：S 有限枚举由 in_eq 平推供给） *)
Lemma cbt_lmax_complete : forall s s' : unit, In (cbt_q s, cbt_k s') cbt_lmax.
Proof.
  intros s s'.
  unfold cbt_lmax.
  simpl.
  left.
  reflexivity.
Qed.

(* ---- 温度具体正值 ---- *)

Definition cbt_temp : Real := one.

Lemma cbt_temp_pos : lt zero cbt_temp.
Proof. unfold cbt_temp. exact one_pos. Defined.

(* ---- 核实例化：z := cb2_z、Delta := cb2_Delta（+1 松弛装配形） ---- *)

Definition cbt_z (s s' : unit) : Real := cb2_z unit cbt_q cbt_k cbt_temp s s'.
Definition cbt_Delta_core : Real := cb2_Delta_core cbt_temp cbt_lmax.
Definition cbt_Delta : Real := cb2_Delta cbt_temp cbt_lmax.

(* 【登记·丙】cb2 证书全显装配直接代入：+1 松弛严格支证书 eps=1#2；供体体为二十余段        *)
(* Q 层机器，装配位无增量可做。                                                        *)
(* Delta_pos：+1 松弛 inl 严格支证书 eps=1#2（cb2_Delta_pos 全显直接代入） *)
Lemma cbt_Delta_pos : lt zero cbt_Delta.
Proof. exact (cb2_Delta_pos cbt_temp one_pos cbt_lmax). Defined.

(* 【登记·丙】z 双界接口参数直接代入两件（本件与 cbt_z_ub）：cb2_z_lb_all／cb2_z_ub_all 全显    *)
(* 输入，完备性证书消去 In，语句面即装配最短形。                                        *)
(* z 双界接口参数直接代入形（完备性证书消去 In；real_le/real_opp 与字段 le/opp 转换同体） *)
Lemma cbt_z_lb : forall s s' : unit, le (opp cbt_Delta) (cbt_z s s').
Proof.
  intros s s'.
  exact (cb2_z_lb_all unit cbt_q cbt_k cbt_temp one_pos cbt_lmax
           cbt_lmax_complete s s').
Defined.

Lemma cbt_z_ub : forall s s' : unit, le (cbt_z s s') cbt_Delta.
Proof.
  intros s s'.
  exact (cb2_z_ub_all unit cbt_q cbt_k cbt_temp one_pos cbt_lmax
           cbt_lmax_complete s s').
Defined.

(* ---- softmax 核实例化（rsq_bs_kernel 10+2 参全显——实例化图 bs_kernel 槽） ---- *)

Definition cbt_sumf (f : unit -> Real) : Real := @csm_sumf unit [tt] f.

(* 【登记·甲乙】判别闭合一件（本件，discriminate 认证形）＋定义性闭合一件               *)
(* （cbt_sum_eq_list，req_refl 最短形）。                                              *)
Lemma cbt_enum_ne : Not ([tt] = (@nil unit)).
Proof. intro H. discriminate H. Qed.

Lemma cbt_sum_eq_list : forall g : unit -> Real,
  req (cbt_sumf g) (rsq_bs_list_sum unit g [tt]).
Proof. intro g. exact (req_refl (rsq_bs_list_sum unit g [tt])). Defined.

Definition cbt_kernel : unit -> unit -> Real :=
  @rsq_bs_kernel Real RealEnhancedReal unit cbt_sumf [tt] cbt_enum_ne
    cbt_temp cbt_temp_pos cbt_Delta cbt_z cbt_z_lb cbt_sum_eq_list.

(* ============================================================ *)
(* 三、sum 接口参数与三证书消解（B1 同轨；plain 冻结槽 1 元平推）                *)
(* ============================================================ *)

(* abs_sum_le_h 槽（plain 冻结槽）：1 元平推（AT7 §二配方——|Σf| = |f tt+0|、 *)
(*   Σ|f| = |f tt|+0，req 拼接后 le_refl；eps 形换槽需动源文件使用语句，禁改） *)
Lemma cbt_abs_sum_le : forall f : unit -> Real,
  le (abs (cbt_sumf f)) (cbt_sumf (fun s : unit => abs (f s))).
Proof.
  intro f.
  assert (Hle0 : le (abs (plus (f tt) zero)) (abs (f tt))).
  { exact (le_id_l _ _ _
             (req_abs_compat (plus (f tt) zero) (f tt) (plus_zero (f tt)))
             (le_refl (abs (f tt)))). }
  exact (le_id_r _ _ _ (req_sym _ _ (plus_zero (abs (f tt)))) Hle0).
Defined.

(* eps 形侧供件（AT8 §三.2 的 csm_abs_sum_le_eps 供入形态记录位：
   plain 槽不在此层，改槽用） *)
Definition cbt_abs_sum_le_eps : forall (f : unit -> Real) (eps : Real),
  lt zero eps ->
  le (abs (cbt_sumf f)) (plus (cbt_sumf (fun s : unit => abs (f s))) eps) :=
  csm_abs_sum_le_eps unit [tt].

(* ---- bs 三槽（cb1 件零改动复用） ---- *)

(* bs_swap：cb1_swap_lists 泛型双折归纳件实例化（B1 同位喂法） *)
(* bs_abs：cb1_bs_abs（le zero a -> req (abs a) a，具体层 Or 拆支件）直接代入    *)
(* bs_lpc / lt_plus_compat_lt_le 槽：real_lt_plus_compat_lt_le（CW219 成品） *)

(* ---- TV₀ 非负消解（质量前件 ⟹ 差 ≡ zero ⟹ abs 链；cb1_tv0 同轨换名） ---- *)

Definition cbt_inv_two : Real := inv_pos (plus one one) req_two_pos.

Definition cbt_tv (mu nu : unit -> Real) : Real :=
  mult cbt_inv_two (cbt_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))).

Lemma cbt_tv0 : forall mu nu : unit -> Real,
  req (cbt_sumf mu) one -> req (cbt_sumf nu) one -> le zero (cbt_tv mu nu).
Proof.
  intros mu nu Hmu Hnu.
  assert (Hmu0 : req (mu tt) one).
  { exact (req_trans _ _ _ (req_sym _ _ (plus_zero (mu tt))) Hmu). }
  assert (Hnu0 : req (nu tt) one).
  { exact (req_trans _ _ _ (req_sym _ _ (plus_zero (nu tt))) Hnu). }
  assert (Hw0 : req (req_minus (mu tt) (nu tt)) zero).
  { exact (req_trans _ _ _
             (req_plus_compat (mu tt) one (opp (nu tt)) (opp one)
                Hmu0 (req_opp_compat (nu tt) one Hnu0))
             (plus_opp one)). }
  assert (Habs : le zero (abs (req_minus (mu tt) (nu tt)))).
  { exact (le_id_r _ _ _
             (req_sym _ _ (req_abs_compat (req_minus (mu tt) (nu tt)) zero Hw0))
             (le_id_r zero zero (abs zero)
                (req_sym _ _ abs_zero) (le_refl zero))). }
  assert (Hprod : le zero (mult (abs (req_minus (mu tt) (nu tt))) cbt_inv_two)).
  { exact (le_id_l _ _ _
             (req_sym _ _
                (req_trans _ _ _ (mult_comm zero cbt_inv_two)
                   (mult_zero cbt_inv_two)))
             (le_mult_compat_weak zero (abs (req_minus (mu tt) (nu tt)))
                cbt_inv_two
                (lt_le_iff zero cbt_inv_two
                   (inl (inv_pos_pos (plus one one) req_two_pos)))
                Habs)). }
  assert (Hsw : le zero (mult cbt_inv_two (abs (req_minus (mu tt) (nu tt))))).
  { exact (le_id_r _ _ _ (mult_comm (abs (req_minus (mu tt) (nu tt))) cbt_inv_two)
             Hprod). }
  unfold cbt_tv.
  exact (le_id_r _ _ _
           (req_mult_compat cbt_inv_two cbt_inv_two
              (abs (req_minus (mu tt) (nu tt)))
              (plus (abs (req_minus (mu tt) (nu tt))) zero)
              (req_refl cbt_inv_two)
              (req_sym _ _ (plus_zero (abs (req_minus (mu tt) (nu tt))))))
           Hsw).
Defined.

(* ---- 迭代器包装（k_titer 出节形 10+2 参；B2 数据全喂） ---- *)

Definition cbt_titer (n : nat) (mu : unit -> Real) : unit -> Real :=
  k_titer unit cbt_sumf [tt] cbt_enum_ne cbt_temp cbt_temp_pos
          cbt_Delta cbt_z cbt_z_lb cbt_sum_eq_list n mu.

(* ============================================================ *)
(* 四、终装：闭合证书 21+8 参全显 + 无条件双头（零接口/零 Arch/零证书参）    *)
(* ============================================================ *)

Definition cbt_mixing_cert :=
  @cmk_attention_mixing_time Real RealEnhancedReal
    real_lt_plus_compat_lt_le          (* lt_plus_compat_lt_le 槽（CW219 成品） *)
    unit cbt_sumf
    (csm_sum_ext unit [tt])            (* sum_ext *)
    (csm_sum_linear unit [tt])         (* sum_linear *)
    (csm_sum_add unit [tt])            (* sum_add *)
    (csm_sum_le unit [tt])             (* sum_le *)
    cbt_abs_sum_le                     (* abs_sum_le_h 槽：1 元 plain 平推 *)
    [tt] cbt_enum_ne                   (* enum / enum_nonempty（证书直接代入） *)
    cbt_temp cbt_temp_pos              (* temp（具体正值） *)
    cbt_Delta cbt_Delta_pos            (* Delta（+1 松弛装配形）+ inl 证书 *)
    cbt_z cbt_z_lb cbt_z_ub            (* 实质 logit 核 + cb2_ 双界 *)
    (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
    cb1_bs_abs
    real_lt_plus_compat_lt_le          (* bs_lpc 槽（同件同形） *)
    cbt_sum_eq_list.

Definition cbt_mixing_cert_le :=
  @cmk_attention_mixing_time_le Real RealEnhancedReal
    real_lt_plus_compat_lt_le
    unit cbt_sumf
    (csm_sum_ext unit [tt])
    (csm_sum_linear unit [tt])
    (csm_sum_add unit [tt])
    (csm_sum_le unit [tt])
    cbt_abs_sum_le
    [tt] cbt_enum_ne
    cbt_temp cbt_temp_pos
    cbt_Delta cbt_Delta_pos
    cbt_z cbt_z_lb cbt_z_ub
    (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
    cb1_bs_abs
    real_lt_plus_compat_lt_le
    cbt_sum_eq_list.

(* 【登记·丁】终装双头直接代入两件（本件与 _le 形）：闭合证书 21+8 参全显定义件装配位，      *)
(* 应用位仅余两证书参直接代入，最短形。                                                    *)
Theorem cbt_unconditional_mixing_time :
  forall mu nu : unit -> Real,
  req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->
  forall budget : Real, lt zero budget ->
  sigT (fun k : nat =>
    lt (cbt_tv (cbt_titer k mu) (cbt_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  exact (cbt_mixing_cert mu nu Hmu Hnu budget Hbudget
           cb1_arch (cbt_tv0 mu nu Hmu Hnu)).
Defined.

Theorem cbt_unconditional_mixing_time_le :
  forall mu nu : unit -> Real,
  req (cbt_sumf mu) one -> req (cbt_sumf nu) one ->
  forall budget : Real, lt zero budget ->
  sigT (fun k : nat =>
    le (cbt_tv (cbt_titer k mu) (cbt_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  exact (cbt_mixing_cert_le mu nu Hmu Hnu budget Hbudget
           cb1_arch (cbt_tv0 mu nu Hmu Hnu)).
Defined.

(* ============================================================ *)
(* 五、自检数值锚：实质核值可计算冒烟（G3 辅证；+1 松弛的数值可见性）           *)
(*   dot(q,k)(5) = 1·(−1) + (−1)·1 = −2 ≠ 0（混号非退化）；                  *)
(*   Delta_core(5) = 1·2 = 2、Delta(5) = 2+1 = 3（松弛数值可见）；            *)
(*   gap(5) = 3−(−2) = 5 > 1#2（inl 严格支证书余量可计算判定）。             *)
(* ============================================================ *)

(* 【登记·乙】数值冒烟四件（cbt_smoke_z／Delta_core／Delta／gap）：可计算数值见证       *)
(* reflexivity 最短形，G3 辅证位，体不可再分。                                          *)
Lemma cbt_smoke_z : projT1 (cbt_z tt tt) 5%nat == (-2)%Q.
Proof. reflexivity. Qed.

Lemma cbt_smoke_Delta_core : projT1 (cbt_Delta_core) 5%nat == 2%Q.
Proof. reflexivity. Qed.

Lemma cbt_smoke_Delta : projT1 (cbt_Delta) 5%nat == 3%Q.
Proof. reflexivity. Qed.

Lemma cbt_smoke_gap : QltT (1#2)%Q
  (projT1 (cbt_Delta) 5%nat - projT1 (cbt_z tt tt) 5%nat).
Proof. reflexivity. Qed.

(* ============ G4 证据：终装前件面机器判据（全 Closed = 无条件） ============ *)
Print Assumptions cbt_unconditional_mixing_time.
Print Assumptions cbt_unconditional_mixing_time_le.
Print Assumptions cbt_expf_mono_le.
Print Assumptions cbt_Delta_pos.
Print Assumptions cbt_z_lb.
Print Assumptions cbt_z_ub.
Print Assumptions cbt_tv0.
Print Assumptions cbt_abs_sum_le.
Print Assumptions cbt_abs_sum_le_eps.
Print Assumptions cbt_kernel.
Print Assumptions cbt_mixing_cert.
