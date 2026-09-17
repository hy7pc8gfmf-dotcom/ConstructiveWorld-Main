(* ============================================================ *)
(* UpReqConcB1.v —— 席 AT7：S5 具体件（bs_swap 双折归纳 + bs_abs req 自证）  *)
(*   + S6 · B1 最小档装配 = 无条件合龙定理成文（第三棒收官）。              *)
(* 论文7 §10.2 第 7 项 · 无条件合龙路线①（AT4 侦察切片工单 S5/S6，           *)
(*   AT5/AT6 交付报告余切片清单）2026-09-18                                 *)
(*                                                              *)
(* 上游（零改四母本）：UpReqConcSoftmax（csm_ 六槽五件委派）、                *)
(*   UpReqConcMixSel（cmk_attention_mixing_time 合龙件 + cmk_le_plus_r +    *)
(*   cmk_scale）、UpReqSampling（k_titer 迭代器 + rsq_bs_list_sum 折叠）、    *)
(*   UpReqSumD（sumd_list_sum 机器 + sumd_list_sum_add/ext）、CW219          *)
(*   （RealEnhancedReal 实例 + real_lt_plus_compat_lt_le + real_arch +      *)
(*   real_const 机器 + real_eq_of_zero_diff 逐点打包机）。                   *)
(*                                                              *)
(* S5（本件上半，泛型 req 面）：                                            *)
(*   ① cb1_list_sum_zero：逐点归零则列表和归零（bs_swap nil 支）。           *)
(*   ② cb1_swap_lists：Σ_a Σ_b f == Σ_b Σ_a f 双折归纳（bs_swap 泛型件，     *)
(*      消费 sumd_list_sum_add + req_plus_compat + IH 对称缝合）。          *)
(*   ③ cb1_bs_abs：le zero a -> req (abs a) a（Or 拆支：lt 支 = abs_pos     *)
(*      字段；req 支 = req_abs_compat + abs_zero 字段 req 链——AT6 卡⑥      *)
(*      Or 墙的「有前提形」合法走廊，AT4 §① bs_abs 行锚位）。               *)
(*                                                              *)
(* S6（本件下半，B1 具体装配，全参喂入 cmk_attention_mixing_time 出节形）：   *)
(*   · 世界：S := unit、enum := [tt]（1 元档）；                            *)
(*   · sumf := csm_sumf unit [tt]（UpReqConcSoftmax 折叠机，AT5 交付）；     *)
(*   · 六槽：ext/linear/add/le = csm_ 委派件；abs_sum_le_h 槽 = 1 元平推     *)
(*     plain 形（cb1_abs_sum_le：|f tt| 双侧 req 同一，绕 AT5 Or 真墙——     *)
(*     AT5 报告 §四 B1 绕墙配方）；                                         *)
(*   · z := fun _ _ => zero、Delta := temp := one（z_lb/z_ub 逐对 lt→le）；  *)
(*   · bs_swap := cb1_swap_lists（S5 泛型件实例化）、bs_abs := cb1_bs_abs；  *)
(*   · bs_lpc 槽 = lt_plus_compat_lt_le 槽同件：real_lt_plus_compat_lt_le   *)
(*     （CW219 Real 层混合加法保序现成件——AT6 报告 §五备选路线定谳：抽象层    *)
(*     不可内证、具体层已成品，零重证）；                                   *)
(*   · Htv0 消解（AT6 报告 §四备选路线择优）：cb1_tv0——1 元档 TV₀ =          *)
(*     ½·|μ tt − ν tt|，由质量前件 Hmu/Hnu（req sumf μ = one 推得 μ tt ≡ one） *)
(*     得差 ≡ zero，abs 面走 abs_zero + req_abs_compat 合法链，plain le     *)
(*     构造达成——零 Or 墙硬凑；                                             *)
(*   · Arch 消解（AT4 §④配方，And-Prop/2≤n 支只弃不搬）：cb1_arch——        *)
(*     real_arch 出 n 与 x < n#1，桥件 cb1_scale_const（cmk_scale n one ≡    *)
(*     n#1，real_const 逐点打包 + Q 层 ring/lia 恒等）换形后直喂，           *)
(*     le zero x 前件弃用（real_arch 本就无条件）。                          *)
(*                                                              *)
(* 终装：csm_b1_unconditional_mixing_time——零接口前件、零 Arch 前件、        *)
(*   零 Htv0 证书参（前件仅剩 μ ν 质量归一与 budget 正性两类数学前件）。      *)
(*   语句（PA 应 Closed = 无条件机器判据）：                                *)
(*     forall mu nu : unit -> Real,                                       *)
(*       req (b1_sumf mu) one -> req (b1_sumf nu) one ->                  *)
(*       forall budget : Real, lt zero budget ->                          *)
(*       sigT (fun k : nat => lt (b1_tv (b1_titer k mu) (b1_titer k nu))  *)
(*                                budget).                                *)
(*                                                              *)
(* 公理面自审：全件语句 Set 值（req/le/lt/sigT/Or 均本库 Set 面）；前提位全  *)
(*   显式证书参数；无未证断言；无经典逻辑、无选择公理、无排中律；零新增      *)
(*   未证假设位。终装 Defined 收束可提取。                                  *)
(* 红线自审：①real_arch 的 (2<=n) 支在 cb1_arch 内整体弃置（prod 拆分后     *)
(*   不入任何 Set 槽——只搬 real_lt 支）；②enum_nonempty（Not-Prop）仅作     *)
(*   证书直喂 k_titer（零消去位）；③面-面逐字：全件 req 面，real_eq 与实例字段逐字对位 *)
(*   与实例字段逐字对位（AT5 卡④全项 exact 纪律）。                         *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设——E-STAGING-AT5 卡①）：          *)
(*   _tat7_run.cmd 前台编译；${PIPESTATUS[0]} 收口；陈旧 .vos 先刷后验        *)
(*   （E-STAGING-AT6 卡③）。                                              *)
(* 撞名检查：cb1_/b1_ 前缀全树 grep 零撞名（20260918 实测）。                 *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia Lra.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* S5 · bs_swap 双折归纳（sumd_list_sum 泛型，任意 enum 可复用 B2 档）       *)
(* ============================================================ *)

Section Cb1Swap.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* 零和腿：逐点 ≡ zero 则列表和 ≡ zero（bs_swap 之 a = nil 支） *)
Lemma cb1_list_sum_zero : forall (S : Set) (g : S -> R) (l : list S),
  (forall x : S, req (g x) zero) -> req (sumd_list_sum S g l) zero.
Proof.
  intros S g l H. induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_trans _ _ _
             (req_plus_compat (g x) zero (sumd_list_sum S g t) zero (H x) IH)
             (plus_zero zero)).
Defined.

(* 双折归纳主件：Σ_a(Σ_b f) == Σ_b(Σ_a f)（bs_swap 泛型件） *)
Lemma cb1_swap_lists : forall (S : Set) (f : S -> S -> R) (a b : list S),
  req (sumd_list_sum S (fun x : S => sumd_list_sum S (fun y : S => f x y) b) a)
      (sumd_list_sum S (fun y : S => sumd_list_sum S (fun x : S => f x y) a) b).
Proof.
  intros S f a. induction a as [| x a' IH]; intro b.
  - (* a = nil：LHS ≡ zero；RHS = Σ_b(Σ_nil ·) 逐点归零腿回拉 *)
    apply req_sym.
    exact (cb1_list_sum_zero S
             (fun y : S => sumd_list_sum S (fun x : S => f x y) nil) b
             (fun y : S => req_refl zero)).
  - (* a = x·a'：sum_add 拆内层 + IH 尾缝（req 对称腿）；链向 RHS→LHS 故 req_sym *)
    exact (req_sym _ _
             (req_trans _ _ _
             (sumd_list_sum_add S (fun y : S => f x y)
                (fun y : S => sumd_list_sum S (fun x0 : S => f x0 y) a') b)
             (req_plus_compat
                (sumd_list_sum S (fun y : S => f x y) b)
                (sumd_list_sum S (fun y : S => f x y) b)
                (sumd_list_sum S (fun y : S => sumd_list_sum S (fun x0 : S => f x0 y) a') b)
                (sumd_list_sum S (fun x0 : S => sumd_list_sum S (fun y : S => f x0 y) b) a')
                (req_refl _)
                (req_sym _ _ (IH b))))).
Defined.

End Cb1Swap.

(* ============================================================ *)
(* S5 · bs_abs req 面自证（具体 Real 层；le 字段为投影非归纳——Or 拆支须     *)
(*   落到 real_le 展开（CW219 同款 unfold 纪律）；泛型层无此消去位，         *)
(*   UpReqSampling 同位 Hypothesis 冻结即此因——本件为具体层消解件）          *)
(* ============================================================ *)

Lemma cb1_bs_abs : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans _ _ _
             (real_eq_trans _ _ _
                (real_abs_eq_compat a real_zero (real_eq_sym real_zero a Heq))
                real_abs_zero_req)
             Heq).
Defined.

(* ============================================================ *)
(* S6 · B1 具体层装配（1 元档：S := unit、enum := [tt]）                    *)
(* ============================================================ *)

(* ---- 世界数据与 sumf ---- *)

Definition b1_sumf (f : unit -> Real) : Real := @csm_sumf unit [tt] f.

Definition b1_inv_two : Real := inv_pos (plus one one) req_two_pos.

Definition b1_enum_ne : Not ([tt] = (@nil unit)).
Proof. intro H. discriminate H. Qed.

(* abs_sum_le_h 槽：1 元 plain 形平推（AT5 §四 B1 绕墙配方）——
   |Σf| = |f tt + 0| ≡ |f tt|、Σ|f| = |f tt| + 0 ≡ |f tt|，req 缝合后 le_refl *)
Lemma cb1_abs_sum_le : forall f : unit -> Real,
  le (abs (b1_sumf f)) (b1_sumf (fun s : unit => abs (f s))).
Proof.
  intro f.
  exact (le_id_r _ _ _
           (req_sym _ _ (plus_zero (abs (f tt))))
           (le_id_l _ _ _
              (req_abs_compat (plus (f tt) zero) (f tt) (plus_zero (f tt)))
              (le_refl (abs (f tt))))).
Defined.

(* sum_eq_list 槽：两折叠机器在一元列表上定义性同一（req_refl 保底，
   探针 P12 实测：元组为具体构造子，fix iota 走通——非 AT6 卡①中性墙位） *)
Lemma cb1_sum_eq_list : forall g : unit -> Real,
  req (b1_sumf g) (rsq_bs_list_sum unit g [tt]).
Proof. intro g. exact (req_refl (rsq_bs_list_sum unit g [tt])). Defined.

(* z 边界证书（B1：z := fun _ _ => zero、Delta := one） *)
Lemma cb1_z_lb : forall s s' : unit, le (opp one) zero.
Proof.
  intros s s'.
  apply (lt_le_iff (opp one) zero).
  apply inl.
  exact (lt_id_r (opp one) (opp zero) zero
           (req_trans (opp zero) (plus zero (opp zero)) zero
              (req_sym _ _ (plus_zero (opp zero))) (plus_opp zero))
           (opp_lt_compat zero one one_pos)).
Defined.

Lemma cb1_z_ub : forall s s' : unit, le zero one.
Proof. intros s s'. apply (lt_le_iff zero one). apply inl. exact one_pos. Defined.

(* ---- real_const 换形机器（Arch 桥基座） ---- *)

(* 逐点打包：real_const 外延（Qeq 保底） *)
Lemma cb1_real_const_ext : forall q1 q2 : Q,
  Qeq q1 q2 -> req (real_const q1) (real_const q2).
Proof.
  intros q1 q2 H. apply real_eq_of_zero_diff. intro k.
  rewrite (real_const_proj q1 k). rewrite (real_const_proj q2 k).
  rewrite H. ring.
Defined.

(* real_const 加法同态（逐点 proj 打包） *)
Lemma cb1_real_const_plus : forall q1 q2 : Q,
  req (real_const (Qplus q1 q2)) (real_plus (real_const q1) (real_const q2)).
Proof.
  intros q1 q2. apply real_eq_of_zero_diff. intro k.
  assert (Hp : projT1 (real_plus (real_const q1) (real_const q2)) k
                 == Qplus (projT1 (real_const q1) k) (projT1 (real_const q2) k))
    by (apply real_plus_proj).
  rewrite Hp.
  rewrite (real_const_proj (Qplus q1 q2) k).
  rewrite (real_const_proj q1 k). rewrite (real_const_proj q2 k).
  ring.
Defined.

(* Q 层恒等二件：nat 后继与 1+z 分裂 *)
Lemma cb1_qeq_nat1 : forall n : nat,
  Qeq (Qmake (Z.of_nat (Datatypes.S n)) 1) (Qmake (1 + Z.of_nat n) 1).
Proof.
  intro n.
  assert (Hz : Z.of_nat (Datatypes.S n) = (1 + Z.of_nat n)%Z) by lia.
  unfold Qeq. rewrite Hz. reflexivity.
Qed.

Lemma cb1_qeq_Zplus1 : forall z : Z,
  Qeq (Qmake (1 + z) 1) (Qplus (Qmake 1%Z 1) (Qmake z 1)).
Proof.
  intro z.
  assert (Hzm : (z * 1 = z)%Z) by ring.
  unfold Qeq. simpl. rewrite Hzm. reflexivity.
Qed.

(* one ≡ 1#1（语句取 real_one 形；喂槽时与字段 one 转换同体） *)
Lemma cb1_one_const : req (real_const (Qmake 1%Z 1)) real_one.
Proof.
  apply real_eq_of_zero_diff. intro k.
  assert (Hz1 : projT1 real_one k == 1%Q) by reflexivity.
  rewrite (real_const_proj (Qmake 1%Z 1) k). rewrite Hz1. ring.
Defined.

(* 桥主件：cmk_scale n one（接口幺链）≡ n#1（real_const 常数链） *)
Lemma cb1_scale_const : forall n : nat,
  req (real_const (Qmake (Z.of_nat n) 1)) (cmk_scale n one).
Proof.
  intro n. induction n as [| n IH].
  - (* 0：real_const 0#1 ≡ zero（逐点 0 差打包） *)
    change (cmk_scale Datatypes.O one) with real_zero.
    apply real_eq_of_zero_diff. intro k.
    change (Z.of_nat Datatypes.O) with 0%Z.
    assert (Hz : projT1 real_zero k == 0%Q) by reflexivity.
    rewrite (real_const_proj (Qmake 0%Z 1) k). rewrite Hz. ring.
  - (* S n：real_const ((n+1)#1) ≡ 1#1 + real_const (n#1) ≡ one + cmk_scale n one *)
    change (cmk_scale (Datatypes.S n) one) with (plus one (cmk_scale n one)).
    exact (req_trans _ _ _
             (cb1_real_const_ext _ _ (cb1_qeq_nat1 n))
             (req_trans _ _ _
                (req_trans _ _ _
                   (cb1_real_const_ext _ _ (cb1_qeq_Zplus1 (Z.of_nat n)))
                   (cb1_real_const_plus (Qmake 1%Z 1) (Qmake (Z.of_nat n) 1)))
                (req_plus_compat (real_const (Qmake 1%Z 1)) one
                   (real_const (Qmake (Z.of_nat n) 1)) (cmk_scale n one)
                   cb1_one_const IH))).
Defined.

(* ---- Arch 消解件（real_arch 换形；And 的 2<=n 支弃置不入槽——红线①） ---- *)

Lemma cb1_arch : forall x : Real, le zero x ->
  sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)).
Proof.
  intros x _. destruct (real_arch x) as [n [Hn2 Hlt]].
  exists n.
  apply (@lt_le_trans Real RealEnhancedReal x
           (real_const (Qmake (Z.of_nat n) 1))
           (cmk_scale (Datatypes.S n) one) Hlt).
  change (cmk_scale (Datatypes.S n) one) with (plus one (cmk_scale n one)).
  apply (le_trans _ (cmk_scale n one)).
  - exact (le_id_l _ _ _ (cb1_scale_const n) (le_refl (cmk_scale n one))).
  - exact (le_id_r _ _ _ (plus_comm (cmk_scale n one) one)
             (cmk_le_plus_r (cmk_scale n one) one
                (lt_le_iff zero one (inl one_pos)))).
Defined.

(* ---- TV₀ 非负消解件（1 元档：质量前件 ⟹ 差 ≡ zero，零 Or 墙硬凑） ---- *)

Definition b1_tv (mu nu : unit -> Real) : Real :=
  mult b1_inv_two (b1_sumf (fun s : unit => abs (req_minus (mu s) (nu s)))).

Lemma cb1_tv0 : forall mu nu : unit -> Real,
  req (b1_sumf mu) one -> req (b1_sumf nu) one -> le zero (b1_tv mu nu).
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
  assert (Hprod : le zero (mult (abs (req_minus (mu tt) (nu tt))) b1_inv_two)).
  { exact (le_id_l _ _ _
             (req_sym _ _
                (req_trans _ _ _ (mult_comm zero b1_inv_two)
                   (mult_zero b1_inv_two)))
             (le_mult_compat_weak zero (abs (req_minus (mu tt) (nu tt))) b1_inv_two
                (lt_le_iff zero b1_inv_two
                   (inl (inv_pos_pos (plus one one) req_two_pos)))
                Habs)). }
  assert (Hsw : le zero (mult b1_inv_two (abs (req_minus (mu tt) (nu tt))))).
  { exact (le_id_r _ _ _ (mult_comm (abs (req_minus (mu tt) (nu tt))) b1_inv_two)
             Hprod). }
  unfold b1_tv.
  exact (le_id_r _ _ _
           (req_mult_compat b1_inv_two b1_inv_two
              (abs (req_minus (mu tt) (nu tt)))
              (plus (abs (req_minus (mu tt) (nu tt))) zero)
              (req_refl b1_inv_two)
              (req_sym _ _ (plus_zero (abs (req_minus (mu tt) (nu tt))))))
           Hsw).
Defined.

(* ---- 迭代器包装（k_titer 出节形；B1 数据全喂） ---- *)

Definition b1_titer (n : nat) (mu : unit -> Real) : unit -> Real :=
  k_titer unit b1_sumf [tt] b1_enum_ne one one_pos one
          (fun _ _ : unit => zero) cb1_z_lb cb1_sum_eq_list n mu.

(* ---- 合龙证书：cmk_attention_mixing_time 25+8 参全显喂入 ---- *)

Definition cb1_mixing_cert :=
  @cmk_attention_mixing_time Real RealEnhancedReal
    real_lt_plus_compat_lt_le          (* lt_plus_compat_lt_le 槽（Real 层成品直喂） *)
    unit b1_sumf
    (csm_sum_ext unit [tt])
    (csm_sum_linear unit [tt])
    (csm_sum_add unit [tt])
    (csm_sum_le unit [tt])
    cb1_abs_sum_le                     (* abs_sum_le_h 槽：1 元 plain 平推 *)
    [tt] b1_enum_ne
    one one_pos                        (* temp := one *)
    one one_pos                        (* Delta := one *)
    (fun _ _ : unit => zero) cb1_z_lb cb1_z_ub
    (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])  (* bs_swap *)
    cb1_bs_abs                         (* bs_abs *)
    real_lt_plus_compat_lt_le          (* bs_lpc 槽（同件同形） *)
    cb1_sum_eq_list.

(* ============ 终装：B1 无条件合龙定理（零接口/零 Arch/零 Htv0 前件） ============ *)

Theorem csm_b1_unconditional_mixing_time :
  forall mu nu : unit -> Real,
  req (b1_sumf mu) one -> req (b1_sumf nu) one ->
  forall budget : Real, lt zero budget ->
  sigT (fun k : nat =>
    lt (b1_tv (b1_titer k mu) (b1_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  exact (cb1_mixing_cert mu nu Hmu Hnu budget Hbudget
           cb1_arch (cb1_tv0 mu nu Hmu Hnu)).
Defined.

(* ≤ 版：le 降温镜像（同一证书链，cmk_attention_mixing_time_le 喂入） *)
Theorem csm_b1_unconditional_mixing_time_le :
  forall mu nu : unit -> Real,
  req (b1_sumf mu) one -> req (b1_sumf nu) one ->
  forall budget : Real, lt zero budget ->
  sigT (fun k : nat =>
    le (b1_tv (b1_titer k mu) (b1_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget.
  apply (@cmk_attention_mixing_time_le Real RealEnhancedReal
           real_lt_plus_compat_lt_le unit b1_sumf
           (csm_sum_ext unit [tt]) (csm_sum_linear unit [tt])
           (csm_sum_add unit [tt]) (csm_sum_le unit [tt])
           cb1_abs_sum_le [tt] b1_enum_ne
           one one_pos one one_pos
           (fun _ _ : unit => zero) cb1_z_lb cb1_z_ub
           (fun f : unit -> unit -> Real => cb1_swap_lists unit f [tt] [tt])
           cb1_bs_abs real_lt_plus_compat_lt_le
           cb1_sum_eq_list mu nu Hmu Hnu budget Hbudget
           cb1_arch (cb1_tv0 mu nu Hmu Hnu)).
Defined.

(* ============ G4 证据：终装前件面机器判据（全 Closed = 无条件） ============ *)
Print Assumptions csm_b1_unconditional_mixing_time.
Print Assumptions csm_b1_unconditional_mixing_time_le.
Print Assumptions cb1_arch.
Print Assumptions cb1_scale_const.
Print Assumptions cb1_swap_lists.
Print Assumptions cb1_bs_abs.
Print Assumptions cb1_tv0.
Print Assumptions cb1_abs_sum_le.
