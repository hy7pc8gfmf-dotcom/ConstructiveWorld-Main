(* ============================================================ *)
(* ToyR 玩具证替换件 —— T264 台账席 战役包Y（tier2 十五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   N_R_pos（原 L135，1 句玩具证）                                       *)
(*   kvev_id_transport（原 L37，2 句玩具证）                              *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T317 恒等守恒更正注记】2026-09-21 包AV六 台账席（头注更正试点件） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，   *)
(* 经 T277（包AL）全量恒等核查定谳、T287（包AV）抽验复核：本件实测   *)
(* 为恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体  *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。          *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面   *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册。         *)
(* 附记：T287 抽验 2 槽守恒  *)
(* ============================================================ *)

(* ============================================================ *)
(* UpKVEv.v *)
(* *)
(* 目的： 核演化面：Z_keep 结构与行演化算子的构造性正性/归一化。 *)
(* 主件： kev_row_normalized / kev_minorization：行归一化与下方化；Z_keep_pos / N_R_pos。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 无外部假设，仅依赖根世界件；核行随机与严格正为 Variable 前提。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpKVEv.v — 方案四拆分前半：K_ev 逐出核机器（机器层）          *)
(*   世界定义 + 行归一化 + minorization 传送。                   *)
(*   全部 Set 层（Id/And/Or/Not/InT/sigT），语句零 Prop 泄露。   *)
(*   构造性：无外部假设，仅依赖 CW_ConstructiveWorld_219。       *)
(*                                                              *)
(*   接口契约（与并行席对齐，逐字）：                            *)
(*     Z_keep    ：keep 过滤行和 Σ if keep then K else 0        *)
(*     Z_keep_pos：HZk_pos 升级为定理（由 keep_nonempty+Kpos    *)
(*                 + single_le_sum_aux 构造性消解，报告已注明）  *)
(*     K_ev      ：if keep s' then K·inv(Z_keep s) else 0       *)
(*     件 0 Z_keep_le_one         ：Z_keep s ≤ 1                *)
(*     件 1 kev_row_normalized    ：行和 == 1                   *)
(*     件 2 kev_minorization      ：δ·U(s') ≤ K_ev s s'         *)
(*     件 2b kev_drop_zero / uncond 版                          *)
(*   δ 形态：Section Variable（delta_pos + delta_le_one +       *)
(*   delta_minor : δ·U ≤ K 逐点——对齐 AttnDoeblin.v 的          *)
(*   minorization 前提先例；仅凭 delta≤1 数学上不闭合，报告）。  *)
(*   U 形态：U s' = real_inv_pos (real_of_nat |states|) 正性     *)
(*   （对齐根内 bs_minorization 的 Unif = inv_pos nR nR_pos）。  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ---------- 助推：非空有限表势的正性（states_ne 的直用形态） ---------- *)
(* 根内 vocab_len_pos 被无关段变量污染（token_eq_dec/count_token）， *)
(* 此处给出洁净版：Not (Id l nil) ⟹ 0 < of_nat |l|。                *)
Lemma kvev_id_transport : forall (A : Set) (x y : A) (P : A -> Set),
  P x -> Id x y -> P y.
Proof.
  intros A x y P p H.
  exact (match H with id_refl => p end).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进入提取闭包，   *)
(* 保证 G3 提取 Obj.magic = 0；根内 single_le_sum_aux 的空 match    *)
(* 会产出 2 处 Obj.magic，故不复用）。                              *)
Lemma kvev_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

Lemma kvev_list_len_pos : forall (A : Set) (l : list A),
  Not (Id l nil) -> real_lt real_zero (real_of_nat (length l)).
Proof.
  intros A l. destruct l as [| w rest].
  - intro Hne. exact (match Hne (@id_refl (list A) nil) with end).
  - intro Hne2. cbn [length].
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest)))
             (real_of_nat (Datatypes.S (length rest)))).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply real_of_nat_nonneg_aux.
    + apply real_eq_refl.
Qed.

(* ============================================================ *)
(* Section KVEv：逐出核世界                                       *)
(* ============================================================ *)
Section KVEv.

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states nil).
Variable K : Tok -> Tok -> Real.                       (* 完整行随机核 *)
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').  (* 核逐点正 *)
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* keep 过滤行和：逐出后的失配质量（行归一化的分母） *)
Definition Z_keep (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.

(* 过滤项逐点非负（件 0 与 Z_keep_pos 的共用引理） *)
Lemma Z_keep_entry_nonneg : forall (s y : Tok),
  real_le real_zero (if keep y then K s y else real_zero).
Proof.
  intros s y. destruct (keep y).
  - apply real_le_from_lt_aux. apply Kpos.
  - apply real_le_refl.
Qed.

(* HZk_pos 升级为定理：keep 见证项 K(s,s0) > 0 且 ≤ Z_keep s *)
Theorem Z_keep_pos : forall s : Tok, real_lt real_zero (Z_keep s).
Proof.
  intro s.
  destruct keep_nonempty as [s0 [Hk0 Hin0]].
  assert (Hb : keep s0 = true) by (apply sf_bool_id_true; exact Hk0).
  assert (Hlt0 : real_lt real_zero (if keep s0 then K s s0 else real_zero)).
  { rewrite Hb. apply Kpos. }
  assert (Hle : real_le (if keep s0 then K s s0 else real_zero) (Z_keep s)).
  { apply (kvev_single_le_sum Tok
             (fun y : Tok => if keep y then K s y else real_zero)
             s0 states Hin0).
    intro y. apply Z_keep_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s) Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s)
             Hlt0 Heq).
Qed.

(* 均匀分布 U ≡ 1/|states|（对齐根内 bs_minorization 的 Unif 形态） *)
Definition N_R : Real := real_of_nat (length states).
Theorem N_R_pos : real_lt real_zero N_R.
Proof.
  exact (kvev_list_len_pos Tok states states_ne).
Qed.
Definition U (s' : Tok) : Real := real_inv_pos N_R N_R_pos.

(* δ 与其前提（对齐 AttnDoeblin.v：delta + 上界 + minorization 前提） *)
Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (U s')) (K s s').

(* 逐出核：保留项 K·inv(Z_keep)，逐出项零 *)
Definition K_ev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
  else real_zero.

(* ---------- 件 0：Z_keep s ≤ 1（keep 子和 ≤ 全和 + Krow 桥） ---------- *)
Theorem Z_keep_le_one : forall s : Tok, real_le (Z_keep s) real_one.
Proof.
  intro s.
  apply (real_le_trans _ (real_list_sum Tok (fun s' : Tok => K s s') states)).
  - apply (real_list_sum_le Tok
             (fun s' : Tok => if keep s' then K s s' else real_zero)
             (fun s' : Tok => K s s') states).
    intro y. destruct (keep y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply Kpos.
  - apply (RealSetoid.real_eq_le _ _). apply Krow.
Qed.

(* ---------- 件 1：行归一化 Σ K_ev == 1 ---------- *)
Theorem kev_row_normalized : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K_ev s s') states) real_one.
Proof.
  intro s.
  (* 第一步：逐点改写 K_ev 为 g(s')·inv(Z)，drop 支经 0·x == 0 归零 *)
  apply (real_eq_trans _
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_mult (if keep s' then K s s' else real_zero)
                           (real_inv_pos (Z_keep s) (Z_keep_pos s)))
              states) _).
  { apply (real_list_sum_ext Tok (fun s' : Tok => K_ev s s') _ states).
    intro y. destruct (keep y) eqn:Hk.
    - unfold K_ev. rewrite Hk. apply real_eq_refl.
    - unfold K_ev. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* 第二步：linear_r 提取常数 inv(Z) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) (Z_keep s)) _).
  { apply (real_list_sum_linear_r Tok
             (real_inv_pos (Z_keep s) (Z_keep_pos s))
             (fun s' : Tok => if keep s' then K s s' else real_zero) states). }
  (* 第三步：inv(Z)·Z == 1（comm 桥 + real_inv_pos_correct） *)
  apply (real_eq_trans _
           (real_mult (Z_keep s) (real_inv_pos (Z_keep s) (Z_keep_pos s))) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- 件 2：minorization 传送 δ·U(s') ≤ K_ev s s' ---------- *)
(* 用 kvev_id_transport 沿 Id (keep s') true 投影到 keep 支，        *)
(* 规避 destruct-eqn 对前提的隐式替换。                              *)
Theorem kev_minorization : forall s s' : Tok,
  Id (keep s') true -> real_le (real_mult delta (U s')) (K_ev s s').
Proof.
  intros s s' Hkeep.
  apply (kvev_id_transport bool true (keep s')
           (fun b : bool =>
              real_le (real_mult delta (U s'))
                (if b then
                   real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s))
                 else real_zero))).
  (* K ≤ K_ev：Z ≤ 1 ⟹ inv(1) ≤ inv(Z)（inv 反单调）⟹ 正乘保序 *)
  - apply (real_le_trans _ (K s s')).
    + apply delta_minor.
    + apply (real_le_trans _
               (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
      * (* K == K·inv(1) 的 eq→le 桥 *)
        apply (RealSetoid.real_eq_le (K s s')
                 (real_mult (K s s') (real_inv_pos real_one real_lt_zero_one))).
        apply real_eq_sym.
        apply (real_eq_trans _ (real_mult (K s s') real_one) _).
        -- apply (RealSetoid.real_eq_mult_compat
                    (K s s') (real_inv_pos real_one real_lt_zero_one)
                    (K s s') real_one).
           ++ apply real_eq_refl.
           ++ apply (real_eq_trans _
                       (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
              ** apply real_eq_sym. apply b4_one_mult.
              ** apply real_inv_pos_correct.
        -- apply real_mult_one.
      * apply (real_le_mult_compat_r (K s s')
                 (real_inv_pos real_one real_lt_zero_one)
                 (real_inv_pos (Z_keep s) (Z_keep_pos s))).
        -- apply real_le_from_lt_aux. apply Kpos.
        -- apply (real_inv_pos_le_compat (Z_keep s) real_one
                    (Z_keep_pos s) real_lt_zero_one).
           apply Z_keep_le_one.
  - exact (id_sym Hkeep).
Qed.

(* ---------- 件 2b：drop 支零形态 + 逐点无条件版 ---------- *)
Theorem kev_drop_zero : forall s s' : Tok,
  Id (keep s') false -> real_eq (K_ev s s') real_zero.
Proof.
  intros s s' Hk.
  apply (kvev_id_transport bool false (keep s')
           (fun b : bool =>
              real_eq (if b then
                         real_mult (K s s')
                           (real_inv_pos (Z_keep s) (Z_keep_pos s))
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hk).
Qed.

Theorem kev_minorization_uncond : forall s s' : Tok,
  real_le (if keep s' then real_mult delta (U s') else real_zero) (K_ev s s').
Proof.
  intros s s'. destruct (keep s') eqn:Hk.
  - apply kev_minorization. apply sf_bool_true_id. exact Hk.
  - apply (RealSetoid.real_eq_le real_zero (K_ev s s')).
    + apply real_eq_sym. apply kev_drop_zero.
      rewrite Hk. apply id_refl.
Qed.

End KVEv.
