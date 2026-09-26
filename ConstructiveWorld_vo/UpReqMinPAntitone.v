(* UpReqMinPAntitone.v —— Min-P 温度反单调件。                    *) (* 使命： 本件形式化 Min-P 采样质量随阈值温度单调递减（p-antitone *)
(*   簇的 req 层伴生：保留判定反单调、保留质量反单调、截断质量    *) (*   单调三向引理）。                                            *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlignRestB、 *) (*   UpReqPropLiftShim。                                         *)
(* 构造性： Set 层语句（le/lt/req/Or 基座 Set 层定义）；核心件     *) (*   Qed、判定件 Defined；纯 term-mode（apply/exact/unfold/      *)
(*   destruct），零改写依赖；可提取。                            *) (* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。  *)
(* 接口申报： 节内假设申报七位（Token/vocab/vocab_nonempty/       *) (*   total_loss/temperature/temperature_pos/pick_max_token）+     *)
(*   序可判定前提 req_le_dec 一位——setoid 类无序判定字段，        *) (*   为 DecidableOrder ord_le_dec 的 req 副本，系序可判定真前提   *)
(*   （整体三分判定不可构造），判定件 req_minp_keep_dec_p         *) (*   Defined 依存之；逐位对应源模块接口，如实申报不硬证。          *)
(* UpReqMinPAntitone.v *) (* 目的： Min-P 温度反单调面（质量随阈值温度单调递减）。 *)
(* 主件： req_minp_keep_p_antitone / req_minp_temp_sum_p_antitone 反单调族。 *) (* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlignRestB、UpReqPropLiftShim。 *)
(* 备注： 词表非空见证与温度正性为显式前提；反单调经适配引理接口在 P 实例层传递。 *) (* MinP p-antitone 簇 5 件的 req 系（setoid 层）伴生族：          *)
(*   temp_factor_max_le_sum 对位注记：req_pick_max_tf_le_minp_sum *) (*   （UpReqAlignRestB）语句逐字同形已证，本件 le_sum 形不再另建；*)
(*   与 req_temp_factor_max_eq 的对位：eq 件 RestB 已有。         *) (* 上游：UpReqAlgebra.v（引擎）+ UpReqAlignRestB.v（minp 系成品   *)
(*   δ 透明依存）。                                              *) (* Id 层 pick_max_token_correct 单点改写一处 → δ 展开             *)
(*   alb_max_markov_prob（RestB 定义体即 alb_markov_kernel @     *) (*   pick_max_token）+ req_markov_pos 消解；Id 层 id_cong/id_refl *)
(*   桥零处需要（le 链全走 le 字段方向：le_mult_compat_weak      *)
(*   固定右因子 + le_trans + req_le_mult_compat_r 固定左因子 +    *)
(*   opp_le_compat）。                                           *)
(* 诚实边界登记表：                                              *)
(*   1. req_le_dec（节内假设申报）：基座 minp_keep_dec_p 的       *)
(*      ord_le_dec（DecidableOrder）req 副本——setoid 类无序      *)
(*      判定字段，判定件 req_minp_keep_dec_p Defined 依存之；     *)
(*      整体序可判定系真前提，如实申报。                          *)
(*   2. minp_dropped_mass_p 的 minus → req_minus（= plus one     *)
(*      (opp ·)，RestB 同款签名变化）；list_sum → rsum（req 世界  *)
(*      和机器，RestB 同构）。                                    *)
(*   3. mp_max_markov_prob/alb_temp_factor 等 6 枚 δ 透明包装 =   *)
(*      UpReqAlignRestB 闭名全参显式提供（签名经检验实证参数表），*)
(*      零物理重复。                                             *)
(* 提取面：多态核件提取 Obj.magic=0（独立检验文件验证）。         *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlignRestB.
From Stdlib Require Import List.
Require Import UpReqPropLiftShim.
(* pls_ 升面适配引理接入：vocab 非空性的 sigT 见证形升面（见 mpa_vocab_ne_witness_s1）。 *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* MinP p-antitone 世界（与基座 MinPSampling _p 簇同构；          *)
(*   接口假设位 = RestB ReqSamplingWorld 子集——_p 族直接          *)
(*   以 mp : R 参数化，min_p 三件与 topk 桥位不依存不立）          *)
(* ============================================================ *)
Section ReqMinPAntitoneWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ---- 接口假设（与源模块 MinPSampling 接口同构的子集） ---- *)
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* vocab 非空性升形位：旧否定形前提经 pls_vocab_ne_lift 升 sigT 见证形——
   深实例化依存位可直取走 sigT 通路；原语句保留。 *)
Definition mpa_vocab_ne_witness_s1 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* ---- 序可判定前提：DecidableOrder 的 req 副本（ord_le_dec 同位；
      RestB req_le_dec 同款）。整体序可判定系真前提，如实申报。 ---- *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* ---- Min-P 选取机器 pick_max_token（与源模块同位；
      只需选取函数本身，argmin 冻结面不触及） ---- *)
Variable pick_max_token : list Token -> Token.

(* ---- RestB minp 系成品 δ 透明包装（闭名全参显式提供；零物理重复） ---- *)
Definition mp_temp_factor (prefix : list Token) (w : Token) : R :=
  UpReqAlignRestB.alb_temp_factor Token total_loss temperature temperature_pos
                              prefix w.

Definition mp_partition_temp (prefix : list Token) : R :=
  UpReqAlignRestB.alb_partition_temp Token vocab total_loss temperature
                                 temperature_pos prefix.

Definition mp_partition_temp_pos (prefix : list Token)
  : lt zero (mp_partition_temp prefix) :=
  UpReqAlignRestB.req_partition_temp_pos Token vocab vocab_nonempty total_loss
                                         temperature temperature_pos prefix.

Definition mp_markov_kernel (prefix : list Token) (w : Token) : R :=
  UpReqAlignRestB.alb_markov_kernel Token vocab vocab_nonempty total_loss
                                temperature temperature_pos prefix w.

Definition mp_markov_pos (prefix : list Token) (w : Token)
  : lt zero (mp_markov_kernel prefix w) :=
  UpReqAlignRestB.req_markov_pos Token vocab vocab_nonempty total_loss
                                 temperature temperature_pos prefix w.

Definition mp_max_markov_prob (prefix : list Token) : R :=
  UpReqAlignRestB.alb_max_markov_prob Token vocab vocab_nonempty total_loss
                                  temperature temperature_pos pick_max_token
                                  prefix.

(* ---- 参数化 Min-P 定义族（与源模块 _p 族同构） ---- *)
Definition req_minp_threshold_p (mp : R) (prefix : list Token) : R :=
  mult mp (mp_max_markov_prob prefix).

Definition req_minp_keep_p (mp : R) (prefix : list Token) (w : Token) : Set :=
  le (req_minp_threshold_p mp prefix) (mp_markov_kernel prefix w).

Definition req_minp_keep_dec_p (mp : R) (prefix : list Token) (w : Token) :
  Or (req_minp_keep_p mp prefix w) (Not (req_minp_keep_p mp prefix w)) :=
  req_le_dec (req_minp_threshold_p mp prefix) (mp_markov_kernel prefix w).

Definition req_minp_temp_sum_p (mp : R) (prefix : list Token) : R :=
  rsum Token (fun w => match req_minp_keep_dec_p mp prefix w with
                       | inl _ => mp_temp_factor prefix w
                       | inr _ => zero
                       end) vocab.

Definition req_minp_dropped_mass_p (mp : R) (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (mp_partition_temp prefix)
                           (mp_partition_temp_pos prefix))
                  (req_minp_temp_sum_p mp prefix)).

(* 基座 temp_factor_nonneg_p 同构件：alb_temp_factor ≥ 0（exp_neg 正性） *)
Lemma req_temp_factor_nonneg_p : forall prefix w,
  le zero (mp_temp_factor prefix w).
Proof.
  intros prefix w.
  apply (lt_le_iff zero (mp_temp_factor prefix w)).
  left.
  unfold mp_temp_factor, UpReqAlignRestB.alb_temp_factor.
  apply exp_neg_pos.
Qed.

(* 基座 minp_term_nonneg_p 同构件：参数化保留者项 ≥ 0（inl 分支 tf ≥ 0，
   inr 分支 0） *)
Lemma req_minp_term_nonneg_p : forall mp prefix w,
  le zero (match req_minp_keep_dec_p mp prefix w with
           | inl _ => mp_temp_factor prefix w
           | inr _ => zero
           end).
Proof.
  intros mp prefix w. destruct (req_minp_keep_dec_p mp prefix w) as [Hk | Hd].
  - exact (req_temp_factor_nonneg_p prefix w).
  - apply le_refl.
Qed.

(* ===== T4a：min_p 增大 ⟹ 保留判定反单调（保留集缩小）=====
   mp1 ≤ mp2 ⟹ threshold1 ≤ threshold2（le_mult_compat_weak，max ≥ 0）
   ⟹ keep2 w（threshold2 ≤ kernel）⟹ threshold1 ≤ kernel（le_trans）
   ⟹ keep1 w。
   alb_max_markov_prob（= alb_markov_kernel @ pick_max_token）+ req_markov_pos。 *)
Lemma req_minp_keep_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix w,
    req_minp_keep_p mp2 prefix w -> req_minp_keep_p mp1 prefix w.
Proof.
  intros mp1 mp2 Hmp prefix w Hk2.
  unfold req_minp_keep_p, req_minp_threshold_p in *.
  (* mp_max_markov_prob ≥ 0（req_markov_pos 经 δ 展开） *)
  assert (Hmax : le zero (mp_max_markov_prob prefix)).
  { unfold mp_max_markov_prob.
    apply (lt_le_iff zero (UpReqAlignRestB.alb_markov_kernel
                             Token vocab vocab_nonempty total_loss
                             temperature temperature_pos prefix
                             (pick_max_token prefix))).
    left. unfold UpReqAlignRestB.alb_max_markov_prob.
    exact (UpReqAlignRestB.req_markov_pos Token vocab vocab_nonempty
                                          total_loss temperature
                                          temperature_pos prefix
                                          (pick_max_token prefix)). }
  (* mp1·max ≤ mp2·max（le_mult_compat_weak，固定右因子 max ≥ 0） *)
  assert (Hthr : le (mult mp1 (mp_max_markov_prob prefix))
                    (mult mp2 (mp_max_markov_prob prefix))).
  { apply (le_mult_compat_weak mp1 mp2 (mp_max_markov_prob prefix)).
    - exact Hmax.
    - exact Hmp. }
  (* threshold1 ≤ threshold2 ≤ kernel ⟹ threshold1 ≤ kernel *)
  apply (le_trans (mult mp1 (mp_max_markov_prob prefix))
                  (mult mp2 (mp_max_markov_prob prefix))
                  (mp_markov_kernel prefix w) Hthr).
  exact Hk2.
Qed.

(* ===== T4b：min_p 增大 ⟹ 保留质量反单调（minp_sum2 ≤ minp_sum1）=====
   逐项：keep2 w ⟹ keep1 w（antitone）⟹ 项贡献相同；keep2 逐出 ⟹
   项2 = 0 ≤ 项1（req_minp_term_nonneg_p）。
   基座 list_sum_le（Id 和）→ rls_le（req 和，RestB 成品）。 *)
Lemma req_minp_temp_sum_p_antitone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (req_minp_temp_sum_p mp2 prefix) (req_minp_temp_sum_p mp1 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold req_minp_temp_sum_p.
  apply (rls_le Token
                (fun w => match req_minp_keep_dec_p mp2 prefix w with
                          | inl _ => mp_temp_factor prefix w
                          | inr _ => zero
                          end)
                (fun w => match req_minp_keep_dec_p mp1 prefix w with
                          | inl _ => mp_temp_factor prefix w
                          | inr _ => zero
                          end)).
  intro w. destruct (req_minp_keep_dec_p mp2 prefix w) as [Hk2 | Hd2].
  - (* keep2 ⟹ keep1（antitone）⟹ 项相同 *)
    assert (Hk1 : req_minp_keep_p mp1 prefix w)
      by exact (req_minp_keep_p_antitone mp1 mp2 Hmp prefix w Hk2).
    destruct (req_minp_keep_dec_p mp1 prefix w) as [Hk1' | Hd1'].
    + apply le_refl.
    + destruct (Hd1' Hk1).
  - (* 逐出 ⟹ 项2 = 0 ≤ 项1 *)
    exact (req_minp_term_nonneg_p mp1 prefix w).
Qed.

(* ===== T4c（主定理，规划书代表件）：min_p 增大 ⟹ 截断质量不降 =====
   sum2 ≤ sum1 ⟹ inv·sum2 ≤ inv·sum1（req_le_mult_compat_r，inv ≥ 0
   固定左因子）⟹ 1−inv·sum1 ≤ 1−inv·sum2（le_plus_compat + opp_le_compat，
   req_minus = plus one (opp ·) δ 展开后 le 字段直接匹配）。 *)
Lemma req_minp_dropped_mass_p_monotone : forall mp1 mp2 : R,
  le mp1 mp2 ->
  forall prefix,
    le (req_minp_dropped_mass_p mp1 prefix)
       (req_minp_dropped_mass_p mp2 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold req_minp_dropped_mass_p, req_minus.
  (* sum2 ≤ sum1（T4b antitone） *)
  assert (Hsum : le (req_minp_temp_sum_p mp2 prefix)
                    (req_minp_temp_sum_p mp1 prefix))
    by exact (req_minp_temp_sum_p_antitone mp1 mp2 Hmp prefix).
  (* inv_p ≥ 0（inv_pos_pos） *)
  assert (Hinv : le zero (inv_pos (mp_partition_temp prefix)
                                  (mp_partition_temp_pos prefix))).
  { apply (lt_le_iff zero (inv_pos (mp_partition_temp prefix)
                                   (mp_partition_temp_pos prefix))).
    left. apply (inv_pos_pos (mp_partition_temp prefix)
                             (mp_partition_temp_pos prefix)). }
  (* inv·sum2 ≤ inv·sum1（req_le_mult_compat_r，固定左因子 inv ≥ 0） *)
  assert (Hscaled : le (mult (inv_pos (mp_partition_temp prefix)
                                         (mp_partition_temp_pos prefix))
                             (req_minp_temp_sum_p mp2 prefix))
                       (mult (inv_pos (mp_partition_temp prefix)
                                      (mp_partition_temp_pos prefix))
                             (req_minp_temp_sum_p mp1 prefix)))
    by exact (req_le_mult_compat_r
                (inv_pos (mp_partition_temp prefix)
                         (mp_partition_temp_pos prefix))
                (req_minp_temp_sum_p mp2 prefix)
                (req_minp_temp_sum_p mp1 prefix) Hinv Hsum).
  (* 1−X ≤ 1−Y（X ≤ Y ⟹ −Y ≤ −X ⟹ 1+(−X) ≤ 1+(−Y)） *)
  apply (le_plus_compat one one
                        (opp (mult (inv_pos (mp_partition_temp prefix)
                                            (mp_partition_temp_pos prefix))
                                   (req_minp_temp_sum_p mp1 prefix)))
                        (opp (mult (inv_pos (mp_partition_temp prefix)
                                            (mp_partition_temp_pos prefix))
                                   (req_minp_temp_sum_p mp2 prefix)))
                        (le_refl one)
                        (opp_le_compat
                           (mult (inv_pos (mp_partition_temp prefix)
                                          (mp_partition_temp_pos prefix))
                                 (req_minp_temp_sum_p mp2 prefix))
                           (mult (inv_pos (mp_partition_temp prefix)
                                          (mp_partition_temp_pos prefix))
                                 (req_minp_temp_sum_p mp1 prefix))
                           Hscaled)).
Qed.

End ReqMinPAntitoneWorld.

Print Assumptions req_temp_factor_nonneg_p.
