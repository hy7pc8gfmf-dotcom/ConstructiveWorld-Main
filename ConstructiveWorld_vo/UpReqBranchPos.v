(* ============================================================ *)
(* ToyR 玩具证替换件 —— T255 台账席 战役包P（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   brp_b4_of_carrier（原 L464，2 句玩具证）                             *)
(*   brp_b4_evicted_partition_pos（原 L439，3 句玩具证）                  *)
(*   brp_b3_evicted_partition_r_pos（原 L383，3 句玩具证）                *)
(*   brp_b2_evicted_partition_pos（原 L335，3 句玩具证）                  *)
(*   brp_b1_Z_aud_pos（原 L288，3 句玩具证）                              *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T329 恒等守恒更正注记】2026-09-22 包AV八 台账席（恒等头注更正全量第二批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测                             *)
(* 为恒等守恒——清单所列 5 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 5 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T329 台账。                   *)
(* 附记：T277 判级全文恒等；包P 整批直推（第二批；承 T321 §五·1）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBranchPos.v *)
(* *)
(* 目的： 消解面零腿分支和的正性（条件分派四腿 B1-B4）。 *)
(* 主件： brp_sum_pos 总和正性与 brp_b1_Z_aud_pos 至 brp_b4_evicted_partition_pos 四腿实例。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD。 *)
(* 备注： 条件值（bool/Or）不可对假设位做 destruct 消去，全部改用 match 分派；正性由接口 le_plus_compat 承担，零新假设位。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBranchPos.v —— G3 消解面零腿分支和正性专席（席72 B1-B4）   *)
(*   使命：sumf (fun s => if keep_dec s then f s else zero) 的正性， *)
(*   双前提=「存在被保留项」（sigT 非空位，Set 层）+「保留项逐项正」，*)
(*   消解后解锁 evicted_partition_pos 族无条件实例化。              *)
(*                                                                *)
(* 数学核：分支和正性 = 列表归纳直证。nil 支矛盾（非空 sigT 前提的   *)
(*   InT 位无 nil 构造子，空型消去）；cons 支两情形——见证头位：头项   *)
(*   严格正 + 尾段和零腿非负（lt_le_trans + le_plus_compat +        *)
(*   le_id_l + plus_zero，纯接口字段）；见证尾位：头项非负 + 尾段和   *)
(*   正（同一单调腿，零条件分支）。零腿的 zero 与正项相加的单调性全   *)
(*   由接口 le_plus_compat 承担，零新假设位。                       *)
(*                                                                *)
(* 条件分派工艺（实测卡点消解）：条件值（bool/Or）不可对假设位做     *)
(*   destruct 消去（假设类型中 scrutinee 停滞），全部改用 match      *)
(*   as-return 显式项：严格正前提与保支标记以双参数吸收进返回型，     *)
(*   真支取正、假支空型消去——零重写战术、零 Prop 表出面。           *)
(*                                                                *)
(* 载体裁决（实测定路线）：四槽原载体均为抽象求和算子（三槽 sumf      *)
(*   Variable + RestB sum_over_S 裸 Variable），无枚举数据，引擎     *)
(*   不可直接消去——沿 E354 装法（席60 ZPosD 先例）：载体具体化为     *)
(*   enum 列表和（sumd_sumf，UpReqSumD 具体实例），消解件语句即       *)
(*   具体实例形；抽象载体回接走规范条件 + lt_id_r 换轨（B4 件 2，    *)
(*   zposd_Z_pos_of_partition 同法）。非空位升级为 sigT 见证形       *)
(*   （sumd_in / 等词否定位的更强构造形态，零 Prop 表出面）。        *)
(*                                                                *)
(* 分级（逐件）：                                                  *)
(*   保底引擎 1：brp_sum_pos（条件无关通用主件：逐点非负 + InT 定位   *)
(*              sigT 见证 ⟹ 列表和正；自持分派件 brp_mem_split       *)
(*              解决 InT 头/尾位 destruct 索引泛化不回连坑）。       *)
(*   引擎两面 2：brp_branch_pos_bool（bool 条件面，B1 对接）        *)
(*              / brp_branch_pos_or（Or 条件面，B2-B4 对接）——       *)
(*              槽形双前提（保支标记见证 + 保留项逐项正）直纳。      *)
(*   条件分派件 4：brp_bool_nonneg_of / brp_bool_pos_of             *)
(*              / brp_or_nonneg_of / brp_or_pos_of（match-return     *)
(*              显式项：真支取正、假支空型消去——假设位 scrutinee     *)
(*              停滞坑的件化消解）。                                *)
(*   消解件 5：B1 brp_b1_Z_aud_pos（UpReqAlign HZ 槽实例形）        *)
(*            B2 brp_b2_evicted_partition_pos（G13_EvictFam 槽）     *)
(*            B3 brp_b3_evicted_partition_r_pos（UpReqAttnGibbs 槽） *)
(*            B4 brp_b4_evicted_partition_pos + brp_b4_of_carrier   *)
(*            （UpReqAlignRestB 槽：sumd 实例形 + 裸载体回接形）。    *)
(*                                                                *)
(* 消费面：增强接口字段（lt_le_trans / le_plus_compat /       *)
(*   le_id_l / lt_id_r / plus_zero / exp_neg_pos / inv_pos / InT，   *)
(*   环恒等式在本世界为 req 级：le_id_l/lt_id_r 走 req 运输）；      *)
(*   UpReqAlgebra（req_plus_zero_l）；UpReqSumD（sumd_sumf /        *)
(*   sumd_list_sum / sumd_list_sum_nonneg / sumd_lt_le）。          *)
(*                                                                *)
(* 红线：Set 层语句（lt/le/req/sigT/prod/InT/Empty_set 皆 Set 值，   *)
(*   非空位零 Prop 表出面）；纯项式组装（exact 供给项，零重写战术）； *)
(*   尾部 Print Assumptions 新件全 Closed；既有文件零改；前缀 brp_   *)
(*   全库防撞已核（grep 零命中）。                                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section BrpEngine：条件无关通用分支和正性引擎                     *)
(* ============================================================ *)
Section BrpEngine.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {A : Set}.

(* 自持分派件：见证位头/尾分派（match-return 显式项，索引精化零回连     *)
(* 需求——here 支取见证正性，next 支取尾段成员，Set 层 Or 返回）。      *)
Definition brp_mem_split (b : A -> R) (a : A) (x : A) (t : list A)
           (hpos : lt zero (b a)) (pin : InT a (x :: t)) :
  Or (lt zero (b x)) (InT a t) :=
  (InT_rec A a
     (fun (L : list A) (_ : InT a L) =>
        match L with
        | nil => Empty_set
        | x' :: t' => Or (lt zero (b x')) (InT a t')
        end)
     (fun l0 : list A => inl hpos)
     (fun (y0 : A) (l0 : list A) (i0 : InT a l0)
        (_ : match l0 with
             | nil => Empty_set
             | x' :: t' => Or (lt zero (b x')) (InT a t')
             end) => inr i0)
     (x :: t) pin).

(* 保底主件（条件无关）：被积项逐点非负 + 「枚举内存在取正项」的      *)
(* InT 定位 sigT 见证 ⟹ 列表和严格正。                              *)
Lemma brp_sum_pos : forall (b : A -> R) (l : list A),
  (forall a : A, le zero (b a)) ->
  sigT (fun a : A => sigT (fun _ : InT a l => lt zero (b a))) ->
  lt zero (sumd_list_sum A b l).
Proof.
  intros b l Hnn. induction l as [| x t IH]; intro Hw.
  - (* nil 支：非空前提矛盾（InT 无 nil 构造子，inversion 滤索引矛盾） *)
    destruct Hw as [a w]. destruct w as [pin hpos]. inversion pin.
  - destruct Hw as [a w]. destruct w as [pin hpos].
    destruct (brp_mem_split b a x t hpos pin) as [hhead | pint].
    + (* 见证头位：头项正 + 尾段和非负 *)
      exact (lt_le_trans zero (b x)
               (plus (b x) (sumd_list_sum A b t))
               hhead
               (le_id_l (b x) (plus (b x) zero)
                  (plus (b x) (sumd_list_sum A b t))
                  (req_sym (plus (b x) zero) (b x) (plus_zero (b x)))
                  (le_plus_compat (b x) (b x) zero
                     (sumd_list_sum A b t)
                     (le_refl (b x))
                     (sumd_list_sum_nonneg A b t Hnn)))).
    + (* 见证尾位：头项非负 + 尾段正 ⟹ 和正（零条件分支） *)
      exact (lt_le_trans zero (sumd_list_sum A b t)
               (plus (b x) (sumd_list_sum A b t))
               (IH (existT
                      (fun a0 : A =>
                         sigT (fun _ : InT a0 t => lt zero (b a0)))
                      a (existT (fun _ : InT a t => lt zero (b a))
                           pint hpos)))
               (le_id_l (sumd_list_sum A b t)
                  (plus zero (sumd_list_sum A b t))
                  (plus (b x) (sumd_list_sum A b t))
                  (req_sym (plus zero (sumd_list_sum A b t))
                     (sumd_list_sum A b t)
                     (req_plus_zero_l (sumd_list_sum A b t)))
                  (le_plus_compat zero (b x) (sumd_list_sum A b t)
                     (sumd_list_sum A b t)
                     (Hnn x)
                     (le_refl (sumd_list_sum A b t))))).
Qed.

End BrpEngine.

(* ============================================================ *)
(* Section BrpEngineBool：引擎 bool 条件面（B1 对接）                *)
(*   槽形双前提直纳：保支标记见证（sigT+InT+标记）+ 保留项逐项正      *)
(*   （match 形，零腿单位型）。条件分派全走 match as-return 显式项。  *)
(* ============================================================ *)
Section BrpEngineBool.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {A : Set}.

Variable c : A -> bool.
Variable f : A -> R.

(* 零腿非负分派件：分支被积项逐点非负（真支正升非负，假支自反） *)
Definition brp_bool_nonneg_of (a : A)
           (Hs : match c a with true => lt zero (f a) | false => unit end) :
  le zero (if c a then f a else zero) :=
  match c a as cx
        return (match cx with true => lt zero (f a) | false => unit end) ->
               le zero (if cx then f a else zero)
  with
  | true => fun h => sumd_lt_le (f a) h
  | false => fun _ => le_refl zero
  end Hs.

(* 取正分派件：严格正前提 + 保支标记 ⟹ 分支项严格正 *)
Definition brp_bool_pos_of (a : A)
           (Hs : match c a with true => lt zero (f a) | false => unit end)
           (mk : match c a with true => unit | false => Empty_set end) :
  lt zero (if c a then f a else zero) :=
  match c a as cx
        return (match cx with true => lt zero (f a) | false => unit end) ->
               (match cx with true => unit | false => Empty_set end) ->
               lt zero (if cx then f a else zero)
  with
  | true => fun h _ => h
  | false => fun _ mk0 => match mk0 with end
  end Hs mk.

Lemma brp_branch_pos_bool : forall (l : list A),
  sigT (fun a : A => prod (InT a l)
          (match c a with true => unit | false => Empty_set end)) ->
  (forall a : A, match c a with true => lt zero (f a) | false => unit end) ->
  lt zero (sumd_list_sum A (fun a : A => if c a then f a else zero) l).
Proof.
  intros l Hw Hstrict.
  destruct Hw as [a [pin mark]].
  exact (brp_sum_pos
           (fun a0 : A => if c a0 then f a0 else zero) l
           (fun a0 : A => brp_bool_nonneg_of a0 (Hstrict a0))
           (existT
              (fun a0 : A =>
                 sigT (fun _ : InT a0 l =>
                          lt zero (if c a0 then f a0 else zero)))
              a
              (existT
                 (fun _ : InT a l =>
                    lt zero (if c a then f a else zero))
                 pin (brp_bool_pos_of a (Hstrict a) mark)))).
Qed.

End BrpEngineBool.

(* ============================================================ *)
(* Section BrpEngineOr：引擎 Or 条件面（B2-B4 对接；槽 keep_dec      *)
(*   forall a, Or (kp a) (Not (kp a)) 逐位同构，Or := A+B）。  *)
(* ============================================================ *)
Section BrpEngineOr.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {A : Set}.

Variable kp : A -> Set.
Variable kd : forall a : A, Or (kp a) (Not (kp a)).
Variable f : A -> R.

(* 零腿非负分派件：分支被积项逐点非负（左支正升非负，右支自反） *)
Definition brp_or_nonneg_of (a : A)
           (Hs : match kd a with inl _ => lt zero (f a) | inr _ => unit end) :
  le zero (if kd a then f a else zero) :=
  match kd a as k0
        return (match k0 with inl _ => lt zero (f a) | inr _ => unit end) ->
               le zero (if k0 then f a else zero)
  with
  | inl _ => fun h => sumd_lt_le (f a) h
  | inr _ => fun _ => le_refl zero
  end Hs.

(* 取正分派件：严格正前提 + 保支标记 ⟹ 分支项严格正 *)
Definition brp_or_pos_of (a : A)
           (Hs : match kd a with inl _ => lt zero (f a) | inr _ => unit end)
           (mk : match kd a with inl _ => unit | inr _ => Empty_set end) :
  lt zero (if kd a then f a else zero) :=
  match kd a as k0
        return (match k0 with inl _ => lt zero (f a) | inr _ => unit end) ->
               (match k0 with inl _ => unit | inr _ => Empty_set end) ->
               lt zero (if k0 then f a else zero)
  with
  | inl _ => fun h _ => h
  | inr _ => fun _ mk0 => match mk0 with end
  end Hs mk.

Lemma brp_branch_pos_or : forall (l : list A),
  sigT (fun a : A => prod (InT a l)
          (match kd a with inl _ => unit | inr _ => Empty_set end)) ->
  (forall a : A, match kd a with
                 | inl _ => lt zero (f a)
                 | inr _ => unit
                 end) ->
  lt zero (sumd_list_sum A (fun a : A => if kd a then f a else zero) l).
Proof.
  intros l Hw Hstrict.
  destruct Hw as [a [pin mark]].
  exact (brp_sum_pos
           (fun a0 : A => if kd a0 then f a0 else zero) l
           (fun a0 : A => brp_or_nonneg_of a0 (Hstrict a0))
           (existT
              (fun a0 : A =>
                 sigT (fun _ : InT a0 l =>
                          lt zero (if kd a0 then f a0 else zero)))
              a
              (existT
                 (fun _ : InT a l =>
                    lt zero (if kd a then f a else zero))
                 pin (brp_or_pos_of a (Hstrict a) mark)))).
Qed.

End BrpEngineOr.

(* ============================================================ *)
(* Section BrpDischargeB1：UpReqAlign HZ 槽实例形（bool 条件面）      *)
(*   槽：Z_aud_req = sumf (fun s => if post_aud s then p s else zero)；*)

(*   sumf 具体化为 sumd_sumf S enum；非空位=sigT 见证（枚举内保支位）。 *)
(*   槽前提 Hp_norm 在见证路线下不需消费（诚实强出：结论不依赖归一）。 *)
(* ============================================================ *)
Section BrpDischargeB1.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.
Variable post_aud : S -> bool.
Variable p : S -> R.

(* 槽形分支和：Z_aud_req 的具体实例形（透明，供下游提供实参直连） *)
Definition brp_Z_aud_req : R :=
  sumd_sumf S enum (fun s : S => if post_aud s then p s else zero).

Lemma brp_b1_Z_aud_pos :
  (forall s : S, lt zero (p s)) ->
  sigT (fun s : S => prod (InT s enum)
          (match post_aud s with true => unit | false => Empty_set end)) ->
  lt zero brp_Z_aud_req.
Proof.
  intros Hp Hw.
  unfold brp_Z_aud_req.
  exact (brp_branch_pos_bool post_aud p enum Hw           (fun s : S =>              match post_aud s as ps                    return (match ps with                            | true => lt zero (p s)                            | false => unit                            end)              with              | true => Hp s              | false => tt              end)).
Qed.

End BrpDischargeB1.

(* ============================================================ *)
(* Section BrpDischargeB2：G13_EvictFam evicted_partition_pos 槽      *)
(*   槽：evicted_partition = sumf (fun s => if keep_dec s then        *)
(*   boltzmann_factor s else zero)；原位 Variable 位。保留项逐项正    *)
(*   = exp_neg_pos（增强接口字段）。                            *)
(* ============================================================ *)
Section BrpDischargeB2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

(* 槽形 boltzmann 因子（G13_EvictFam 同形） *)
Definition brp_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* 槽形分支和：evicted_partition 的具体实例形 *)
Definition brp_evicted_partition : R :=
  sumd_sumf S enum
    (fun s : S => if keep_dec s then brp_boltzmann_factor s else zero).

Lemma brp_b2_evicted_partition_pos :
  sigT (fun s : S => prod (InT s enum)
          (match keep_dec s with
           | inl _ => unit
           | inr _ => Empty_set
           end)) ->
  lt zero brp_evicted_partition.
Proof.
  intro Hw.
  unfold brp_evicted_partition.
  exact (brp_branch_pos_or keep keep_dec brp_boltzmann_factor enum Hw           (fun s : S =>              match keep_dec s as k0                    return (match k0 with                            | inl _ => lt zero (brp_boltzmann_factor s)                            | inr _ => unit                            end)              with              | inl _ => exp_neg_pos (mult (inv_pos D D_pos) (energy s))              | inr _ => tt              end)).
Qed.

End BrpDischargeB2.

(* ============================================================ *)
(* Section BrpDischargeB3：UpReqAttnGibbs evicted_partition_r_pos 槽  *)
(*   槽：evicted_partition_r = sumf (fun s => if keep_dec s then      *)
(*   boltzmann_factor_r s else zero)；B2 同构镜像（Gibbs 面 _r 名）。 *)
(* ============================================================ *)
Section BrpDischargeB3.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

(* 槽形 boltzmann 因子（UpReqAttnGibbs boltzmann_factor_r 同形） *)
Definition brp_boltzmann_factor_r (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* 槽形分支和：evicted_partition_r 的具体实例形 *)
Definition brp_evicted_partition_r : R :=
  sumd_sumf S enum
    (fun s : S => if keep_dec s then brp_boltzmann_factor_r s else zero).

Lemma brp_b3_evicted_partition_r_pos :
  sigT (fun s : S => prod (InT s enum)
          (match keep_dec s with
           | inl _ => unit
           | inr _ => Empty_set
           end)) ->
  lt zero brp_evicted_partition_r.
Proof.
  intro Hw.
  unfold brp_evicted_partition_r.
  exact (brp_branch_pos_or keep keep_dec brp_boltzmann_factor_r enum Hw           (fun s : S =>              match keep_dec s as k0                    return (match k0 with                            | inl _ => lt zero (brp_boltzmann_factor_r s)                            | inr _ => unit                            end)              with              | inl _ => exp_neg_pos (mult (inv_pos D D_pos) (energy s))              | inr _ => tt              end)).
Qed.

End BrpDischargeB3.

(* ============================================================ *)
(* Section BrpDischargeB4：UpReqAlignRestB req_evicted_partition_pos  *)
(*   槽：req_evicted_partition = sum_over_S (fun s => match           *)
(*   keep_dec s with inl _ => req_kv_boltzmann_factor s | inr _ =>    *)
(*   zero end)；载体 sum_over_S 为裸 Variable（无枚举/无字段）。       *)
(*   两形结果：件 1 = sumd 具体实例形（E354 装法）；                  *)
(*   件 2 = 裸载体回接形（规范条件 + lt_id_r 换轨，                    *)
(*   zposd_Z_pos_of_partition 同法；RestB 侧补规范位即直装）。        *)
(* ============================================================ *)
Section BrpDischargeB4.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).

(* 槽形 KV boltzmann 因子（req_kv_boltzmann_factor 同形） *)
Definition brp_kv_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* 槽形分支和：match 显式形（RestB 槽逐位同构） *)
Definition brp_req_evicted_partition_sumd : R :=
  sumd_sumf S enum
    (fun s : S => match keep_dec s with
                  | inl _ => brp_kv_boltzmann_factor s
                  | inr _ => zero
                  end).

(* 件 1：sumd 具体实例形消解 *)
Lemma brp_b4_evicted_partition_pos :
  sigT (fun s : S => prod (InT s enum)
          (match keep_dec s with
           | inl _ => unit
           | inr _ => Empty_set
           end)) ->
  lt zero brp_req_evicted_partition_sumd.
Proof.
  intro Hw.
  unfold brp_req_evicted_partition_sumd.
  exact (brp_branch_pos_or keep keep_dec brp_kv_boltzmann_factor enum Hw           (fun s : S =>              match keep_dec s as k0                    return (match k0 with                            | inl _ => lt zero (brp_kv_boltzmann_factor s)                            | inr _ => unit                            end)              with              | inl _ => exp_neg_pos (mult (inv_pos D D_pos) (energy s))              | inr _ => tt              end)).
Qed.

(* 件 2：裸载体回接形——任给求和算子 sov 携规范条件（req (sov g)      *)
(* (sumd_sumf g)，RestB 侧补位形态，partition_condition 同位），       *)
(* 槽原形（sov 载体）正性直推。 *)
Lemma brp_b4_of_carrier : forall (sov : (S -> R) -> R),
  (forall g : S -> R, req (sov g) (sumd_sumf S enum g)) ->
  sigT (fun s : S => prod (InT s enum)
          (match keep_dec s with
           | inl _ => unit
           | inr _ => Empty_set
           end)) ->
  lt zero (sov (fun s : S => match keep_dec s with
                             | inl _ => brp_kv_boltzmann_factor s
                             | inr _ => zero
                             end)).
Proof.
  intros sov Hspec Hw.
  exact (lt_id_r zero           (sumd_sumf S enum              (fun s : S => match keep_dec s with                            | inl _ => brp_kv_boltzmann_factor s                            | inr _ => zero                            end))           (sov (fun s : S => match keep_dec s with                              | inl _ => brp_kv_boltzmann_factor s                              | inr _ => zero                              end))           (req_sym              (sov (fun s : S => match keep_dec s with                                 | inl _ => brp_kv_boltzmann_factor s                                 | inr _ => zero                                 end))              (sumd_sumf S enum                 (fun s : S => match keep_dec s with                               | inl _ => brp_kv_boltzmann_factor s                               | inr _ => zero                               end))              (Hspec (fun s : S => match keep_dec s with                                   | inl _ => brp_kv_boltzmann_factor s                                   | inr _ => zero                                   end)))           (brp_b4_evicted_partition_pos Hw)).
Qed.

End BrpDischargeB4.

(* ============ G3 证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions brp_sum_pos.
Print Assumptions brp_branch_pos_bool.
Print Assumptions brp_branch_pos_or.
Print Assumptions brp_b1_Z_aud_pos.
Print Assumptions brp_b2_evicted_partition_pos.
Print Assumptions brp_b3_evicted_partition_r_pos.
Print Assumptions brp_b4_evicted_partition_pos.
Print Assumptions brp_b4_of_carrier.
