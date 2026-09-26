(* ==========================================================================)
   UpReqBranchPos.v — 分支正性引擎件
   使命: BrpEngine 三世界（list/bool/Or）：brp_sum_pos、brp_branch_pos_bool/or；BrpDischarge B1-B4 四组：审计 Z 正性、Boltzmann 因子-逐出分划正性、KV 逐出分划正性（brp_b4_evicted_partition_pos）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD；Stdlib List。
   对标: 分情况正性证明的引擎化（逐分支见证构造）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

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
(*   参数形双前提直纳：保支标记见证（sigT+InT+标记）+ 保留项逐项正      *)
(*   （match 形，零肢单位型）。条件分派全走 match as-return 显式项。  *)
(* ============================================================ *)
Section BrpEngineBool.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {A : Set}.

Variable c : A -> bool.
Variable f : A -> R.

(* 零肢非负分派件：分支被积项逐点非负（真支正升非负，假支自反） *)
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
(* Section BrpEngineOr：引擎 Or 条件面（B2-B4 对接；参数 keep_dec      *)
(*   forall a, Or (kp a) (Not (kp a)) 逐位同构，Or := A+B）。  *)
(* ============================================================ *)
Section BrpEngineOr.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {A : Set}.

Variable kp : A -> Set.
Variable kd : forall a : A, Or (kp a) (Not (kp a)).
Variable f : A -> R.

(* 零肢非负分派件：分支被积项逐点非负（左支正升非负，右支自反） *)
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
(* Section BrpDischargeB1：UpReqAlign HZ 参数位实例形（bool 条件面）      *)
(*   参数位：Z_aud_req = sumf (fun s => if post_aud s then p s else zero)；*)

(*   sumf 具体化为 sumd_sumf S enum；非空位=sigT 见证（枚举内保支位）。 *)
(*   参数位前提 Hp_norm 在见证路线下不需依存（诚实强出：结论不依赖归一）。 *)
(* ============================================================ *)
Section BrpDischargeB1.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.
Variable post_aud : S -> bool.
Variable p : S -> R.

(* 参数形分支和：Z_aud_req 的具体实例形（透明，供下游提供实参直连） *)
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
(* Section BrpDischargeB2：G13_EvictFam evicted_partition_pos 参数位      *)
(*   参数位：evicted_partition = sumf (fun s => if keep_dec s then        *)
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

(* 参数形 boltzmann 因子（G13_EvictFam 同形） *)
Definition brp_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* 参数形分支和：evicted_partition 的具体实例形 *)
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
(* Section BrpDischargeB3：UpReqAttnGibbs evicted_partition_r_pos 参数位  *)
(*   参数位：evicted_partition_r = sumf (fun s => if keep_dec s then      *)
(*   boltzmann_factor_r s else zero)；B2 同构副本（Gibbs 面 _r 名）。 *)
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

(* 参数形 boltzmann 因子（UpReqAttnGibbs boltzmann_factor_r 同形） *)
Definition brp_boltzmann_factor_r (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* 参数形分支和：evicted_partition_r 的具体实例形 *)
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
(*   参数位：req_evicted_partition = sum_over_S (fun s => match           *)
(*   keep_dec s with inl _ => req_kv_boltzmann_factor s | inr _ =>    *)
(*   zero end)；载体 sum_over_S 为裸 Variable（无枚举/无字段）。       *)
(*   两形结果：件 1 = sumd 具体实例形（既有装法）；                  *)
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

(* 参数形 KV boltzmann 因子（req_kv_boltzmann_factor 同形） *)
Definition brp_kv_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

(* 参数形分支和：match 显式形（RestB 参数位逐位同构） *)
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
(* 参数位原形（sov 载体）正性直推。 *)
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
