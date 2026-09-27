(* ==========================================================================)
   EpsOptimalReach.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：reqd_of_nat_succ、reqd_of_nat_pos、req_le_one_mult_le_inv_mp、reqd_mp_of_nat_pos、req_rsum_le_const_mp、mpd_vocab_ne_witness_s1、mpd_temp_factor、mpd_partition_temp、mpd_partition_temp_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import UpReqDist.
Require Import UpReqAlignRestB.
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Require Import UpReqPropLiftShim.
From Stdlib Require Import List QArith Lia.

(* ================= §1 reqd_of_nat_succ 族 ================= *)
(* ================= §1 reqd_of_nat_succ 族 ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* B6W 对接（AA13 显式假设①首批）：pls_ 升面适配层接入， *)
(* 供三节 vocab_nonempty 老否定形前提升 sigT 见证形使用。 *)

(* 引擎段 ReqMpEngineNum：nat→req-R 嵌入（reqd_of_nat）公共桥接件  *)
Section ReqMpEngineNum.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* E1 步进桥：reqd_of_nat (S n) 与 1 + reqd_of_nat n 逐点 δ 相等 *)
Lemma reqd_of_nat_succ : forall n : nat,
  req (reqd_of_nat (Datatypes.S n)) (plus one (reqd_of_nat n)).
Proof.
  intro n. exact (req_refl (reqd_of_nat (Datatypes.S n))).
Qed.

(* E2 嵌入正性＝attn_nat_to_R_pos 对位（S13）：0 < reqd_of_nat (S k)。
   归纳结构对位原证：基座换形（1+0 == 1，one_pos）；步 plus_positive。 *)
Lemma reqd_of_nat_pos : forall k : nat, lt zero (reqd_of_nat (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - (* 基座：reqd_of_nat 1 == 1 + 0，换形回 one 后 one_pos *)
    apply (lt_id_r zero one (reqd_of_nat (Datatypes.S O))).
    + apply (req_trans one (plus one zero) (reqd_of_nat (Datatypes.S O))).
      * apply (req_sym (plus one zero) one). apply plus_zero.
      * apply req_refl.
    + exact one_pos.
  - (* 步：reqd_of_nat (S (S k)) ≡ 1 + reqd_of_nat (S k)，双双正性 *)
    apply (lt_id_r zero (plus one (reqd_of_nat (Datatypes.S k)))
                      (reqd_of_nat (Datatypes.S (Datatypes.S k)))).
    + apply req_refl.
    + apply plus_positive.
      * exact one_pos.
      * exact IH.
Qed.

(* E3 <- le_one_mult_le_inv_mp（S06 / ）：
   0 < G、1 ≤ G·M ⟹ inv G ≤ M。
   Id 系三步（assoc / comm+inv_correct / one 消去）逐位换 req_trans 链；
   Id 中间件 Habs 换 req Habs；收尾 le_id_r/le_id_l 运输 +
   req_le_mult_compat_r（正因子左乘保序，UpReqAlgebra L465）。 *)
Lemma req_le_one_mult_le_inv_mp : forall (G M : R) (Hg : lt zero G),
  le one (mult G M) -> le (inv_pos G Hg) M.
Proof.
  intros G M Hg Hle.
  assert (Habs : req (mult (inv_pos G Hg) (mult G M)) M).
  { apply (req_trans (mult (inv_pos G Hg) (mult G M))
                     (mult (mult (inv_pos G Hg) G) M)).
    - apply mult_assoc.
    - apply (req_trans (mult (mult (inv_pos G Hg) G) M)
                       (mult (mult G (inv_pos G Hg)) M)).
      + apply (req_mult_compat (mult (inv_pos G Hg) G)
                               (mult G (inv_pos G Hg)) M M).
        * apply mult_comm.
        * apply req_refl.
      + apply (req_trans (mult (mult G (inv_pos G Hg)) M) (mult one M)).
        * apply (req_mult_compat (mult G (inv_pos G Hg)) one M M).
          -- exact (inv_pos_correct G Hg).
          -- apply req_refl.
        * apply req_mult_one_l. }
  apply (le_id_r (inv_pos G Hg) (mult (inv_pos G Hg) (mult G M)) M Habs).
  apply (le_id_l (inv_pos G Hg) (mult (inv_pos G Hg) one)
                 (mult (inv_pos G Hg) (mult G M))).
  - apply (req_sym (mult (inv_pos G Hg) one) (inv_pos G Hg)).
    apply mult_one.
  - apply (req_le_mult_compat_r (inv_pos G Hg) one (mult G M)).
    + apply (lt_le_iff zero (inv_pos G Hg)). left. apply (inv_pos_pos G Hg).
    + exact Hle.
Qed.

End ReqMpEngineNum.

(* 实例段 ReqMpNatDomain：nat 计数域两件（I1 / I2）              *)
Section ReqMpNatDomain.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.

(* I1 <- mp_of_nat_pos（S06 / ）：
   「缺 nat→req-R 桥」即由本件消除）；长度非空 ⟹ 形如 S k，归 E2。 *)
Lemma reqd_mp_of_nat_pos : forall l : list Token,
  Not (Id l nil) -> lt zero (reqd_of_nat (length l)).
Proof.
  intros l Hl. destruct l as [| w rest].
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - simpl. exact (reqd_of_nat_pos (length rest)).
Qed.

(* I2 <- list_sum_le_const_mp（S06 / ）：
   逐项 f w ≤ M ⟹ Σ f l ≤ of_nat(|l|)·M。
   求和载体 list_sum → rsum（RestB Part 0 req 机器）；
   步基 Id 换形（mult_plus_distr_r / mult_one 消去）逐位换 req 链；
   mp_of_nat → reqd_of_nat（同桥）。 *)
Lemma req_rsum_le_const_mp : forall (f : Token -> R) (M : R) (l : list Token),
  (forall w : Token, InT w l -> le (f w) M) ->
  le (rsum Token f l) (mult (reqd_of_nat (length l)) M).
Proof.
  intros f M l. induction l as [| w rest IH]; intros Hf; simpl.
  - (* 基座：0 ≤ 0·M == 0 *)
    apply (le_id_l zero (mult zero M) (mult zero M)).
    + apply (req_sym (mult zero M) zero).
      apply (req_trans (mult zero M) (mult M zero) zero).
      * apply mult_comm.
      * apply mult_zero.
    + apply le_refl.
  - (* 步：f w ≤ M + 余和 ≤ N·M ⟹ 和 ≤ (1+N)·M == M + N·M *)
    apply (le_id_r (plus (f w) (rsum Token f rest))
                   (plus M (mult (reqd_of_nat (length rest)) M))
                   (mult (plus one (reqd_of_nat (length rest))) M)).
    + apply (req_trans (plus M (mult (reqd_of_nat (length rest)) M))
                       (plus (mult one M) (mult (reqd_of_nat (length rest)) M))).
      * apply (req_plus_compat M (mult one M)
                               (mult (reqd_of_nat (length rest)) M)
                               (mult (reqd_of_nat (length rest)) M)).
        -- apply (req_sym (mult one M) M). apply req_mult_one_l.
        -- apply req_refl.
      * apply (req_sym (mult (plus one (reqd_of_nat (length rest))) M)
                       (plus (mult one M) (mult (reqd_of_nat (length rest)) M))).
        apply req_mult_plus_distr_r.
    + apply le_plus_compat.
      * apply (Hf w). apply InT_here.
      * apply IH. intros w' Hw'. apply (Hf w'). apply InT_next. exact Hw'.
Qed.

End ReqMpNatDomain.

(* 实例段 ReqMpKernelWorld：Min-P 核域（I3 / I4）                *)
(*   接口假设与基座 MinPSampling L5934-5945 同位（Token/vocab/   *)
(*   total_loss/temperature 六参闭包）；mpd_* 定义族 δ 透明同形  *)
(*   于 RestB alb_temp_factor/alb_partition_temp/alb_markov_     *)
(*   kernel（闭包显式参数先例）。                                *)
Section ReqMpKernelWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W 对接位（AA13 #11）：老否定形前提经 pls_ 适配层升 sigT 见证形—— *)
(* 深对接使用位：pls_vocab_ne_lift 把节内旧形 Variable 原地升为见证形， *)
(* 下游新代码可直取 mpd_vocab_ne_witness_s1 走 sigT 通路。旧语句原样保留。 *)
Definition mpd_vocab_ne_witness_s1 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.

(* 基座 temp_factor L30703 同位：e^{-inv(T)·loss} *)
Definition mpd_temp_factor (prefix : list Token) (w : Token) : R :=
  exp_neg (mult (inv_pos temperature temperature_pos)
                (total_loss (prefix ++ [w]))).

(* 基座 partition_temp L30705 同位：Σ_w temp_factor *)
Definition mpd_partition_temp (prefix : list Token) : R :=
  rsum Token (mpd_temp_factor prefix) vocab.

(* 基座 partition_temp_pos L30768 对位（RestB req_partition_temp_pos 同证形） *)
Lemma mpd_partition_temp_pos : forall prefix : list Token,
  lt zero (mpd_partition_temp prefix).
Proof.
  intro prefix. unfold mpd_partition_temp.
  apply (rls_pos Token (mpd_temp_factor prefix)).
  - intro w. unfold mpd_temp_factor. apply exp_neg_pos.
  - apply vocab_nonempty.
Qed.

(* 基座 markov_kernel L30859 同位：tf·inv(partition) *)
Definition mpd_markov_kernel (prefix : list Token) (w : Token) : R :=
  mult (mpd_temp_factor prefix w)
       (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)).

(* I3 <- markov_kernel_normalized_mp（S06 / ）：
   Σ_w kernel w == 1。原证 Hext（mult_comm 逐点）/ Hlin（和线性）/
   Hp（inv_pos_correct）三步逐位对位：
   Id rewrite/id_cong → req_trans；list_sum_linear → rls_linear；
   list_sum_ext → rls_ext。 *)
Lemma req_markov_kernel_normalized_mp : forall prefix : list Token,
  req (rsum Token (mpd_markov_kernel prefix) vocab) one.
Proof.
  intro prefix. unfold mpd_markov_kernel.
  apply (req_trans
    (rsum Token (fun w : Token =>
        mult (mpd_temp_factor prefix w)
             (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))) vocab)
    (mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
          (rsum Token (mpd_temp_factor prefix) vocab))
    one
    (req_trans
      (rsum Token (fun w : Token =>
          mult (mpd_temp_factor prefix w)
               (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))) vocab)
      (rsum Token (fun w : Token =>
          mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
               (mpd_temp_factor prefix w)) vocab)
      (mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
            (rsum Token (mpd_temp_factor prefix) vocab))
      (rls_ext Token
         (fun w : Token => mult (mpd_temp_factor prefix w)
              (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))
         (fun w : Token => mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
              (mpd_temp_factor prefix w))
         (fun w : Token => mult_comm (mpd_temp_factor prefix w)
              (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))
         vocab)
      (rls_linear Token (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
                  (mpd_temp_factor prefix) vocab))
    (req_trans (mult (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
                     (mpd_partition_temp prefix))
               (mult (mpd_partition_temp prefix)
                     (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))
               one
               (mult_comm (inv_pos (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix))
                          (mpd_partition_temp prefix))
               (inv_pos_correct (mpd_partition_temp prefix) (mpd_partition_temp_pos prefix)))).
Qed.

(* I4 <- temp_factor_antitone_mp（S06 / ）：
   loss a ≤ loss b ⟹ tf b ≤ tf a（exp_neg 递减 + 正因子左乘保序） *)
Lemma req_temp_factor_antitone_mp : forall (prefix : list Token) (a b : Token),
  le (total_loss (prefix ++ [a])) (total_loss (prefix ++ [b])) ->
  le (mpd_temp_factor prefix b) (mpd_temp_factor prefix a).
Proof.
  intros prefix a b Hloss. unfold mpd_temp_factor.
  apply (exp_neg_le_decr (mult (inv_pos temperature temperature_pos)
                               (total_loss (prefix ++ [a])))
                         (mult (inv_pos temperature temperature_pos)
                               (total_loss (prefix ++ [b])))).
  apply (req_le_mult_compat_r (inv_pos temperature temperature_pos)
                              (total_loss (prefix ++ [a]))
                              (total_loss (prefix ++ [b]))).
  - apply (lt_le_iff zero (inv_pos temperature temperature_pos)). left.
    apply (inv_pos_pos temperature temperature_pos).
  - exact Hloss.
Qed.

End ReqMpKernelWorld.


(* ------------------------------------------------------------
      argmin 遍历最小性——ord_le_dec 换 req_le_dec 桥假设（RestB
      T2① 同位），le_refl/le_trans 接口字段直换；InT 解构保持
      Id 层（list 机器不迁，§1.1 边界 2）。难度：中。
      snd 恒等不变式——纯 Id 层归纳（中支判定换 req_le_dec），
      语句 Id 等式保持（best_loss = ... 为 Id）。难度：低-中。
      pick_best 最优性——依赖 1+2 + vocab 解构；难度：中。
      kernel w ≤ max——依赖 3 + I4（temp_factor_antitone）+
      le_mult_compat 弱形（接口字段在盘）；难度：低（引擎齐备）。
      1 == Σkernel（I3）≤ |S|·max（I2 实例）⟹ inv(|S|) ≤ max
      （E3）；链式组装，Id/req 等式桥按 RestB 归一化定理同形。
      难度：中（三支全在盘）。
      链②）：dropped ≤ 1 − p_max（RestB req_minp_dropped_mass_le_
      one_minus_max 已在盘）+ 链① + opp_le_compat 组装；难度：中。
   附：argmin_aux_token / pick_best_token / max_markov_prob 三定义
   的 req 节内对位定义（RestB alb_max_markov_prob 已有 max 同位；
   argmin 需新建，后续可在 ReqMpKernelWorld 续节扩充）。
   ============================================================ *)
(* X3b2 段：mp 域余 6 件全清（argmin 簇 3 + 组装 3） *)
(* ------------------------------------------------------------
     1 mpd_argmin_aux_token_min_mp <- argmin_aux_token_min_mp
        （S06 / ；判定换 req_le_dec 桥假设位 1；
        原件 not_le_lt 步（S01 判定序域字段，req 域无同名字段）以
        桥假设位 2 req_lt_dec 三分解替之——RestB ReqSamplingWorld
        桥假设位 2 同位；le_refl/le_trans/le_id_l 接口字段直换）
        （纯 Id 层归纳，中支判定换 req_le_dec；语句 Id 等式保持）
        （依赖 1+2 + vocab 解构；snd 恒等以 Id 层 rewrite 运输，
        list-Id 机器不迁边界内）
        （le_mult_compat_weak 接口字段直用 + I4 req_temp_factor_
        antitone_mp + 件 3）
        （I3 归一化 + I2 req_rsum_le_const_mp + E3 req_le_one_mult_
        le_inv_mp 三支组装；mp_of_nat → reqd_of_nat 桥）
     6 mpd_minp_dropped_mass_le_inv_vocab_size <- S06 /
         链②（dropped ≤ 1−max 支按 RestB req_minp_dropped_
        mass_le_one_minus_max 同证形移植（alb_→mpd_ 逐位改名），+
        链① + opp_le_compat 组装）
   定义簇（S06-6061/L6167-6171/L6174-6191/L6504 对位；
   RestB alb_ 闭包显式参数先例，mpd_markov_kernel 等首批 discharged
   定义以全闭包显式使用）：
     mpd_argmin_aux_token / mpd_pick_best_token（default_token 参，
     S06 同位）/ mpd_pick_max_token / mpd_max_markov_prob /
     mpd_minp_threshold / mpd_minp_keep / mpd_minp_keep_dec /
     mpd_minp_temp_sum / mpd_minp_dropped_mass
   桥假设：位 1 req_le_dec（RestB 位 1 同位）；位 2 req_lt_dec
   ============================================================ *)
Section ReqMpKernelWorld2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W 对接位（AA13 #12）：同 #11 深对接——旧形升 sigT 见证形使用位。 *)
Definition mpd_vocab_ne_witness_s2 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.
Variable min_p : R.
Variable min_p_lt_one : lt min_p one.

(* 桥假设位 1：DecidableOrder ord_le_dec（S01 L331 同位）的 req 对应副本 *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* 桥假设位 2：三分判定（RestB ReqSamplingWorld 位 2 同位） *)
Hypothesis req_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* ---- 定义簇 1：argmin 机器（S06 L6044-6061 对位；candidate_token 内联） ---- *)
Fixpoint mpd_argmin_aux_token (prefix : list Token) (l : list Token)
         (best : (Token * R)%type) : (Token * R)%type :=
  match l with
  | nil => best
  | w :: rest =>
      match req_le_dec (total_loss (prefix ++ [w])) (snd best) with
      | inl _ => mpd_argmin_aux_token prefix rest (w, total_loss (prefix ++ [w]))
      | inr _ => mpd_argmin_aux_token prefix rest best
      end
  end.

Definition mpd_pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest => fst (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* InT 头前插（S06 L6086 对位；Id 层机器保持，不迁边界 2） *)
Lemma mpd_InT_head_extend : forall (x y a : Token) (l : list Token),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - apply InT_next. apply InT_next. assumption.
Qed.

(* 1 <- argmin_aux_token_min_mp（S06 / ）：
   And 两支遍历归纳；换 best 中支 w = a 的 not_le_lt 步以 req_lt_dec
   三分解替代（inl lt → lt_le_iff；mid req → le_id_l + le_refl；
   inr lt → 与 Hnot 相左而消空）。 *)
Lemma mpd_argmin_aux_token_min_mp : forall (prefix : list Token) (l : list Token)
         (best_token : Token) (best_loss : R),
  And (forall w : Token, InT w l ->
         le (snd (mpd_argmin_aux_token prefix l (best_token, best_loss)))
            (total_loss (prefix ++ [w])))
      (le (snd (mpd_argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - assert (Hempty : forall w : Token, InT w nil ->
      le (snd (mpd_argmin_aux_token prefix nil (best_token, best_loss)))
         (total_loss (prefix ++ [w]))).
    { intros w HIn. exact (match HIn with end). }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (req_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- destruct (req_lt_dec best_loss (total_loss (prefix ++ [a])))
                    as [Hlt | [Heq | Hgt]].
           ++ exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
           ++ exact (le_trans _ best_loss _ IH_le
                       (le_id_l best_loss (total_loss (prefix ++ [a]))
                                (total_loss (prefix ++ [a])) Heq
                                (le_refl (total_loss (prefix ++ [a]))))).
           ++ exact (match Hnot (lt_le_iff _ _ (inl Hgt)) with end).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* 2 <- argmin_aux_token_snd_correct_mp（S06 / ）：
   snd 恒等不变式；纯 Id 层归纳，中支判定换 req_le_dec。 *)
Lemma mpd_argmin_aux_token_snd_correct_mp : forall (prefix : list Token) (l : list Token)
         (best_token : Token) (best_loss : R),
  best_loss = total_loss (prefix ++ [best_token]) ->
  snd (mpd_argmin_aux_token prefix l (best_token, best_loss)) =
  total_loss (prefix ++ [fst (mpd_argmin_aux_token prefix l (best_token, best_loss))]).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (req_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) eq_refl).
    + exact (IH best_token best_loss Hinit).
Qed.

(* 遍历成员辅件（S06 L6077 argmin_aux_token_mem 对位） *)
Lemma mpd_argmin_aux_token_mem : forall (prefix : list Token) (l : list Token)
         (best_token : Token) (best_loss : R),
  InT (fst (mpd_argmin_aux_token prefix l (best_token, best_loss))) (best_token :: l).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - simpl. apply InT_here.
  - simpl. destruct (req_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + apply InT_next. apply IH.
    + apply mpd_InT_head_extend. apply IH.
Qed.

(* pick_best ∈ vocab（S06 L6096 pick_best_in_vocab' 对位） *)
Lemma mpd_pick_best_in_vocab : forall prefix : list Token,
  InT (mpd_pick_best_token prefix) vocab.
Proof.
  intro prefix. unfold mpd_pick_best_token.
  destruct vocab as [| w0 rest].
  - exact (match vocab_nonempty (@id_refl (list Token) nil) with end).
  - apply (mpd_argmin_aux_token_mem prefix rest w0 (total_loss (prefix ++ [w0]))).
Qed.

(* 3 <- pick_best_optimal_mp（S06 / ）：
   依赖 1+2；vocab 解构两支；snd 恒等以 Id 层 rewrite 运输。 *)
Theorem mpd_pick_best_optimal_mp : forall (prefix : list Token) (w : Token),
  InT w vocab ->
  le (total_loss (prefix ++ [mpd_pick_best_token prefix]))
     (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold mpd_pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - destruct (mpd_argmin_aux_token_min_mp prefix rest w0 (total_loss (prefix ++ [w0])))
      as [Hmin Hle].
    assert (Hsnd : snd (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))) =
                   total_loss (prefix ++ [fst (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))]))
      by exact (mpd_argmin_aux_token_snd_correct_mp prefix rest w0
                  (total_loss (prefix ++ [w0])) eq_refl).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + assert (Hr : le (snd (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w0]))) by exact Hle.
      rewrite Hsnd in Hr.
      exact Hr.
    + assert (Hr : le (snd (mpd_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [w]))) by exact (Hmin w Hwrest).
      rewrite Hsnd in Hr.
      exact Hr.
Qed.

(* ---- 定义簇 2：max（S06 L6167-6171 对位；首批 discharged 定义全闭包使用） ---- *)
Definition mpd_pick_max_token (prefix : list Token) : Token := mpd_pick_best_token prefix.

Definition mpd_max_markov_prob (prefix : list Token) : R :=
  mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                    (mpd_pick_max_token prefix).

(* 4 <- markov_kernel_le_max_mp（S06 / ）：
   le_mult_compat_weak 接口字段（le zero c → le a b → le a·c ≤ b·c）
   直用；单调支路 = I4 + 件 3。 *)
Lemma mpd_markov_kernel_le_max_mp : forall (prefix : list Token) (w : Token),
  InT w vocab ->
  le (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w)
     (mpd_max_markov_prob prefix).
Proof.
  intros prefix w Hw.
  unfold mpd_max_markov_prob, mpd_markov_kernel.
  apply (le_mult_compat_weak
           (mpd_temp_factor Token total_loss temperature temperature_pos prefix w)
           (mpd_temp_factor Token total_loss temperature temperature_pos prefix
                              (mpd_pick_max_token prefix))
           (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                    (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
  - apply (lt_le_iff zero
             (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
    left. apply (inv_pos_pos
                   (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                   (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
  - apply (req_temp_factor_antitone_mp Token total_loss temperature temperature_pos
                                       prefix (mpd_pick_max_token prefix) w).
    apply (mpd_pick_best_optimal_mp prefix w Hw).
Qed.

(* 5 <- minp_max_ge_inv_vocab_size（S06 / ，链①）：
   inv(|S|) ≤ max。三支：I3 归一化（Σkernel == 1）+ I2 逐项和界
   （Σkernel ≤ |S|·max，逐项 = 件 4）+ E3 除以正数。 *)
Lemma mpd_minp_max_ge_inv_vocab_size : forall prefix : list Token,
  le (inv_pos (reqd_of_nat (length vocab))
              (reqd_mp_of_nat_pos Token vocab vocab_nonempty))
     (mpd_max_markov_prob prefix).
Proof.
  intro prefix.
  apply (req_le_one_mult_le_inv_mp (reqd_of_nat (length vocab)) (mpd_max_markov_prob prefix)
                                   (reqd_mp_of_nat_pos Token vocab vocab_nonempty)).
  apply (le_id_l one
                 (rsum Token
                    (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                       temperature_pos prefix) vocab)
                 (mult (reqd_of_nat (length vocab)) (mpd_max_markov_prob prefix))).
  - apply (req_sym (rsum Token
                     (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                        temperature_pos prefix) vocab) one).
    apply (req_markov_kernel_normalized_mp Token vocab vocab_nonempty total_loss temperature
                                           temperature_pos prefix).
  - apply (req_rsum_le_const_mp Token
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix)
             (mpd_max_markov_prob prefix) vocab).
    intro w. intro Hw. apply (mpd_markov_kernel_le_max_mp prefix w Hw).
Qed.

(* ---- 定义簇 3：minp 截断机器（S06 L6174-6191/L6504 对位；RestB alb_ 同构） ---- *)
Definition mpd_minp_threshold (prefix : list Token) : R :=
  mult min_p (mpd_max_markov_prob prefix).

Definition mpd_minp_keep (prefix : list Token) (w : Token) : Set :=
  le (mpd_minp_threshold prefix)
     (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).

Definition mpd_minp_keep_dec (prefix : list Token) (w : Token) :
  Or (mpd_minp_keep prefix w) (Not (mpd_minp_keep prefix w)) :=
  req_le_dec (mpd_minp_threshold prefix)
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).

Definition mpd_minp_temp_sum (prefix : list Token) : R :=
  rsum Token (fun w : Token =>
           match mpd_minp_keep_dec prefix w with
           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
           | inr _ => zero
           end) vocab.

Definition mpd_minp_dropped_mass (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_minp_temp_sum prefix)).

(* 核正性辅件（RestB req_markov_pos 同证形） *)
Lemma mpd_markov_pos : forall (prefix : list Token) (w : Token),
  lt zero (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix w).
Proof.
  intros prefix w. unfold mpd_markov_kernel. apply mult_positive.
  - unfold mpd_temp_factor. apply exp_neg_pos.
  - apply (inv_pos_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                       (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
Qed.

(* pick_max 保留性（RestB req_pick_max_minp_keep 同证形：
   kernel ≥ 0、min_p < 1 ⟹ min_p·kernel ≤ kernel） *)
Lemma mpd_pick_max_minp_keep : forall prefix : list Token,
  mpd_minp_keep prefix (mpd_pick_max_token prefix).
Proof.
  intro prefix. unfold mpd_minp_keep, mpd_minp_threshold.
  apply (req_le_mult_le_one_r
           (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                              (mpd_pick_max_token prefix))
           min_p).
  - apply (lt_le_iff zero
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                                (mpd_pick_max_token prefix))).
    left. apply (mpd_markov_pos prefix (mpd_pick_max_token prefix)).
  - apply (lt_le_iff min_p one). left. exact min_p_lt_one.
Qed.

(* pick_max 的 tf 单项 ≤ 截断和（RestB req_pick_max_tf_le_minp_sum
   同证形：keep 判定 Or 分解 + rls_single_le 单项下界） *)
Lemma mpd_pick_max_tf_le_minp_sum : forall prefix : list Token,
  le (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
     (mpd_minp_temp_sum prefix).
Proof.
  intro prefix. unfold mpd_minp_temp_sum.
  assert (Heq : req (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                    (match mpd_minp_keep_dec prefix (mpd_pick_max_token prefix) with
                     | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)
                     | inr _ => zero
                     end)).
  { destruct (mpd_minp_keep_dec prefix (mpd_pick_max_token prefix)) as [Hk | Hd].
    - apply req_refl.
    - destruct (Hd (mpd_pick_max_minp_keep prefix)). }
  apply (le_id_l (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                 (match mpd_minp_keep_dec prefix (mpd_pick_max_token prefix) with
                  | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)
                  | inr _ => zero
                  end)
                 (rsum Token (fun w : Token =>
                           match mpd_minp_keep_dec prefix w with
                           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
                           | inr _ => zero
                           end) vocab)).
  - exact Heq.
  - apply (rls_single_le Token
           (fun w : Token => match mpd_minp_keep_dec prefix w with
                             | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
                             | inr _ => zero
                             end)
           (mpd_pick_max_token prefix) vocab).
    + apply mpd_pick_best_in_vocab.
    + intro w. destruct (mpd_minp_keep_dec prefix w) as [Hk2 | Hd2].
      * apply (lt_le_iff zero (mpd_temp_factor Token total_loss temperature temperature_pos prefix w)). left.
        unfold mpd_temp_factor. apply exp_neg_pos.
      * apply le_refl.
Qed.

(* tf(pick_max) == max·partition（RestB req_temp_factor_max_eq 同证形；
   max_prob δ 展开 == tf·inv_p 为 conversion，req_refl 收尾） *)
Lemma mpd_temp_factor_max_eq : forall prefix : list Token,
  req (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
      (mult (mpd_max_markov_prob prefix)
            (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)).
Proof.
  intro prefix.
  apply (req_trans
    (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
    (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
          (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                         (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
    (mult (mpd_max_markov_prob prefix)
          (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))).
  - apply (req_trans
      (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
      (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)) one)
      (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
            (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))).
    + apply (req_sym
               (mult (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix)) one)
               (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))).
      apply mult_one.
    + apply req_mult_compat.
      * apply req_refl.
      * apply (req_trans
          one
          (mult (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                         (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
          (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                         (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))).
        -- apply (req_sym
                    (mult (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                          (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                   (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                    one).
           apply inv_pos_correct.
        -- apply mult_comm.
  - apply mult_assoc.
Qed.

(* max ≤ inv_p·截断和（RestB req_minp_scaled_sum_ge_max 同证形：
   Hid 代数链 + H1 单项下界 + 正因子左乘） *)
Lemma mpd_minp_scaled_sum_ge_max : forall prefix : list Token,
  le (mpd_max_markov_prob prefix)
     (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                    (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
           (mpd_minp_temp_sum prefix)).
Proof.
  intro prefix.
  assert (Hid : req (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                   (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                          (mult (mpd_max_markov_prob prefix)
                                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
                    (mpd_max_markov_prob prefix)).
  { apply (req_trans
      (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                     (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
            (mult (mpd_max_markov_prob prefix)
                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
      (mult (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_max_markov_prob prefix))
            (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
      (mpd_max_markov_prob prefix)).
    - apply mult_assoc.
    - apply (req_trans
        (mult (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                             (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                    (mpd_max_markov_prob prefix))
              (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
        (mult (mult (mpd_max_markov_prob prefix)
                    (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                             (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
              (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
        (mpd_max_markov_prob prefix)).
      + apply req_mult_compat.
        * apply mult_comm.
        * apply req_refl.
      + apply (req_trans
          (mult (mult (mpd_max_markov_prob prefix)
                      (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
          (mult (mpd_max_markov_prob prefix)
                (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
          (mpd_max_markov_prob prefix)).
        * apply (req_sym
            (mult (mpd_max_markov_prob prefix)
                  (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                 (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                        (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
            (mult (mult (mpd_max_markov_prob prefix)
                        (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                 (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))).
          apply mult_assoc.
        * apply (req_trans
            (mult (mpd_max_markov_prob prefix)
                  (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                 (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                        (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
            (mult (mpd_max_markov_prob prefix) one)
            (mpd_max_markov_prob prefix)).
          -- apply req_mult_compat.
             ++ apply req_refl.
             ++ apply (req_trans
                 (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                       (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                 (mult (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                       (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)))
                 one).
                ** apply mult_comm.
                ** apply inv_pos_correct.
          -- apply mult_one. }
  assert (H1 : le (mult (mpd_max_markov_prob prefix)
                        (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                  (mpd_minp_temp_sum prefix)).
  { exact (le_id_l (mult (mpd_max_markov_prob prefix)
                         (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                   (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                   (mpd_minp_temp_sum prefix)
                   (req_sym (mpd_temp_factor Token total_loss temperature temperature_pos prefix (mpd_pick_max_token prefix))
                            (mult (mpd_max_markov_prob prefix)
                                  (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
                            (mpd_temp_factor_max_eq prefix))
                   (mpd_pick_max_tf_le_minp_sum prefix)). }
  apply (le_id_l (mpd_max_markov_prob prefix)
                 (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                       (mult (mpd_max_markov_prob prefix)
                             (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
                 (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                       (mpd_minp_temp_sum prefix))).
  - apply (req_sym (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                  (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                         (mult (mpd_max_markov_prob prefix)
                               (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)))
                   (mpd_max_markov_prob prefix)).
    exact Hid.
  - apply (req_le_mult_compat_r
             (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
             (mult (mpd_max_markov_prob prefix)
                   (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix))
             (mpd_minp_temp_sum prefix)).
    + apply (lt_le_iff zero
               (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                        (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
      left. apply (inv_pos_pos
                     (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                     (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
    + exact H1.
Qed.

(* dropped ≤ 1 − max（RestB req_minp_dropped_mass_le_one_minus_max
   同证形：opp 反向 + 平移） *)
Lemma mpd_minp_dropped_mass_le_one_minus_max : forall prefix : list Token,
  le (mpd_minp_dropped_mass prefix) (req_minus one (mpd_max_markov_prob prefix)).
Proof.
  intro prefix. unfold mpd_minp_dropped_mass.
  apply (le_plus_compat one one
           (opp (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_minp_temp_sum prefix)))
           (opp (mpd_max_markov_prob prefix))).
  - apply le_refl.
  - apply opp_le_compat.
    exact (mpd_minp_scaled_sum_ge_max prefix).
Qed.

(* 6 <- minp_dropped_mass_le_inv_vocab_size（S06 / ，链②）：
   dropped ≤ 1 − max ≤ 1 − inv(|S|)；后半 opp 反向 + 链①。 *)
Theorem mpd_minp_dropped_mass_le_inv_vocab_size : forall prefix : list Token,
  le (mpd_minp_dropped_mass prefix)
     (req_minus one
                (inv_pos (reqd_of_nat (length vocab))
                         (reqd_mp_of_nat_pos Token vocab vocab_nonempty))).
Proof.
  intro prefix.
  apply (le_trans _ (req_minus one (mpd_max_markov_prob prefix)) _).
  - exact (mpd_minp_dropped_mass_le_one_minus_max prefix).
  - apply (le_plus_compat one one
                           (opp (mpd_max_markov_prob prefix))
                           (opp (inv_pos (reqd_of_nat (length vocab))
                                         (reqd_mp_of_nat_pos Token vocab vocab_nonempty)))).
    + apply le_refl.
    + apply (opp_le_compat (inv_pos (reqd_of_nat (length vocab))
                                    (reqd_mp_of_nat_pos Token vocab vocab_nonempty))
                           (mpd_max_markov_prob prefix)).
      exact (mpd_minp_max_ge_inv_vocab_size prefix).
Qed.

End ReqMpKernelWorld2.

(* 文件尾原余件清单（上文）由本节全数闭合，特此注记。            *)

(* 批 4 余件：单项界 1 件对位裁决 + p-antitone 簇 5 件全新建）。   *)
(* ------------------------------------------------------------
       二批辅件 mpd_pick_max_tf_le_minp_sum（ReqMpKernelWorld2）语句
       逐位同形（le (tf pick_max) (minp_temp_sum)），对位成立、就此
     1 mpd_minp_keep_p_antitone <- minp_keep_p_antitone
       max ≥ 0 支路由 mpd_markov_pos 经 δ 展开免费取得）
     2 mpd_temp_factor_nonneg_p <- temp_factor_nonneg_p
     3 mpd_minp_term_nonneg_p <- minp_term_nonneg_p
     4 mpd_minp_temp_sum_p_antitone <- minp_temp_sum_p_antitone
       keep2 ⟹ keep1 反单调 + term_nonneg 逐点两分支同形）
     5 mpd_minp_dropped_mass_p_monotone <- minp_dropped_mass_p_monotone
       opp_le_compat 反向 + le_plus_compat 平移三支组装）
   定义簇（S06-6751 对位；p 簇阈值以 mp : R 显式参替代固定
   min_p，故本节节假设不携 min_p/min_p_lt_one——比 S06 节更省；
   二批 discharged 定义全闭包显式使用，mpd_pick_max_token 六参形 /
   mpd_max_markov_prob 十参形经 -vos 检验实证写死）：
     mpd_minp_threshold_p / mpd_minp_keep_p / mpd_minp_keep_dec_p /
     mpd_minp_temp_sum_p / mpd_minp_dropped_mass_p
   桥假设：req_le_dec（位 1，ReqMpKernelWorld2 同位）；p 簇不涉
   argmin 三分步，无需位 2。
   ============================================================ *)
Section ReqMpKernelWorld3.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
(* B6W 对接位（AA13 #13）：同 #11 深对接——旧形升 sigT 见证形使用位。 *)
Definition mpd_vocab_ne_witness_s3 : pls_vocab_ne vocab
  := pls_vocab_ne_lift vocab vocab_nonempty.
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.

(* 桥假设位 1（ReqMpKernelWorld2 位 1 同位） *)
Hypothesis req_le_dec : forall a b : R, Or (le a b) (Not (le a b)).

(* ---- p 簇定义（S06 L6726-6751 对位；阈值 mp : R 显式参） ---- *)
Definition mpd_minp_threshold_p (mp : R) (prefix : list Token) : R :=
  mult mp (mpd_max_markov_prob Token vocab vocab_nonempty total_loss temperature
                                  temperature_pos default_token req_le_dec prefix).

Definition mpd_minp_keep_p (mp : R) (prefix : list Token) (w : Token) : Set :=
  le (mpd_minp_threshold_p mp prefix)
     (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                        temperature_pos prefix w).

Definition mpd_minp_keep_dec_p (mp : R) (prefix : list Token) (w : Token) :
  Or (mpd_minp_keep_p mp prefix w) (Not (mpd_minp_keep_p mp prefix w)) :=
  req_le_dec (mpd_minp_threshold_p mp prefix)
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix w).

Definition mpd_minp_temp_sum_p (mp : R) (prefix : list Token) : R :=
  rsum Token (fun w : Token =>
           match mpd_minp_keep_dec_p mp prefix w with
           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
           | inr _ => zero
           end) vocab.

Definition mpd_minp_dropped_mass_p (mp : R) (prefix : list Token) : R :=
  req_minus one
            (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                           (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                  (mpd_minp_temp_sum_p mp prefix)).

(* 2 <- temp_factor_nonneg_p（S06 / ）：
   tf ≥ 0（exp_neg 恒正 + lt_le_iff 提升） *)
Lemma mpd_temp_factor_nonneg_p : forall (prefix : list Token) (w : Token),
  le zero (mpd_temp_factor Token total_loss temperature temperature_pos prefix w).
Proof.
  intros prefix w.
  apply (lt_le_iff zero (mpd_temp_factor Token total_loss temperature temperature_pos prefix w)).
  left. unfold mpd_temp_factor. apply exp_neg_pos.
Qed.

(* 3 <- minp_term_nonneg_p（S06 / ）：
   参数化保留者项 ≥ 0（inl 分支 tf ≥ 0，inr 分支 0） *)
Lemma mpd_minp_term_nonneg_p : forall (mp : R) (prefix : list Token) (w : Token),
  le zero (match mpd_minp_keep_dec_p mp prefix w with
           | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
           | inr _ => zero
           end).
Proof.
  intros mp prefix w. destruct (mpd_minp_keep_dec_p mp prefix w) as [Hk | Hd].
  - exact (mpd_temp_factor_nonneg_p prefix w).
  - apply le_refl.
Qed.

(* 1 <- minp_keep_p_antitone（S06 / ，T4a）：
   mp1 ≤ mp2 ⟹ keep_p mp2 w ⟹ keep_p mp1 w（阈值增大保留集缩小）。
   max ≥ 0 支路：mpd_max_markov_prob δ 展开 == kernel(pick_max)，
   mpd_markov_pos 免费；单调支路 le_mult_compat_weak 接口字段直用。 *)
Lemma mpd_minp_keep_p_antitone : forall (mp1 mp2 : R),
  le mp1 mp2 ->
  forall (prefix : list Token) (w : Token),
    mpd_minp_keep_p mp2 prefix w -> mpd_minp_keep_p mp1 prefix w.
Proof.
  intros mp1 mp2 Hmp prefix w Hk2.
  assert (Hmax : le zero (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                temperature temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix))).
  { apply (lt_le_iff zero (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                temperature temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix))).
    left. exact (mpd_markov_pos Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix)). }
  apply (le_trans (mult mp1 (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                  temperature temperature_pos prefix
                                  (mpd_pick_max_token Token vocab total_loss default_token
                                                         req_le_dec prefix)))
                  (mult mp2 (mpd_markov_kernel Token vocab vocab_nonempty total_loss
                                  temperature temperature_pos prefix
                                  (mpd_pick_max_token Token vocab total_loss default_token
                                                         req_le_dec prefix)))
                  (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                     temperature_pos prefix w)).
  - apply (le_mult_compat_weak mp1 mp2
             (mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature
                                temperature_pos prefix
                                (mpd_pick_max_token Token vocab total_loss default_token
                                                       req_le_dec prefix)) Hmax Hmp).
  - exact Hk2.
Qed.

(* 4 <- minp_temp_sum_p_antitone（S06 / ，T4b）：
   mp1 ≤ mp2 ⟹ 截断和反单调（sum_p mp2 ≤ sum_p mp1）。
   逐点两分支：keep2 ⟹ keep1（件 1）⟹ 项同（le_refl）；
   keep2 逐出 ⟹ 项 2 = 0 ≤ 项 1（件 3）。 *)
Lemma mpd_minp_temp_sum_p_antitone : forall (mp1 mp2 : R),
  le mp1 mp2 ->
  forall prefix : list Token,
    le (mpd_minp_temp_sum_p mp2 prefix) (mpd_minp_temp_sum_p mp1 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold mpd_minp_temp_sum_p.
  apply (rls_le Token
           (fun w : Token =>
              match mpd_minp_keep_dec_p mp2 prefix w with
              | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
              | inr _ => zero
              end)
           (fun w : Token =>
              match mpd_minp_keep_dec_p mp1 prefix w with
              | inl _ => mpd_temp_factor Token total_loss temperature temperature_pos prefix w
              | inr _ => zero
              end)).
  intro w. destruct (mpd_minp_keep_dec_p mp2 prefix w) as [Hk2 | Hd2].
  - assert (Hk1 : mpd_minp_keep_p mp1 prefix w)
      by exact (mpd_minp_keep_p_antitone mp1 mp2 Hmp prefix w Hk2).
    destruct (mpd_minp_keep_dec_p mp1 prefix w) as [Hk1' | Hd1'].
    + apply le_refl.
    + destruct (Hd1' Hk1).
  - exact (mpd_minp_term_nonneg_p mp1 prefix w).
Qed.

(* 5 <- minp_dropped_mass_p_monotone（S06 / ，T4c）：
   mp1 ≤ mp2 ⟹ 截断质量单调（mass_p mp1 ≤ mass_p mp2）。
   三支：sum_p 反单调（件 4）→ inv_p 左乘保序（req_le_mult_compat_r）
   → 1−X 反向（opp_le_compat + le_plus_compat 平移）。 *)
Lemma mpd_minp_dropped_mass_p_monotone : forall (mp1 mp2 : R),
  le mp1 mp2 ->
  forall prefix : list Token,
    le (mpd_minp_dropped_mass_p mp1 prefix) (mpd_minp_dropped_mass_p mp2 prefix).
Proof.
  intros mp1 mp2 Hmp prefix. unfold mpd_minp_dropped_mass_p.
  assert (Hsum : le (mpd_minp_temp_sum_p mp2 prefix) (mpd_minp_temp_sum_p mp1 prefix))
    by exact (mpd_minp_temp_sum_p_antitone mp1 mp2 Hmp prefix).
  assert (Hscaled : le (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                          (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                             (mpd_minp_temp_sum_p mp2 prefix))
                       (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                             (mpd_minp_temp_sum_p mp1 prefix))).
  { apply (req_le_mult_compat_r
             (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                      (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
    - apply (lt_le_iff zero (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                                     (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))).
      left. apply (inv_pos_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix)).
    - exact Hsum. }
  apply (le_plus_compat one one
           (opp (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_minp_temp_sum_p mp1 prefix)))
           (opp (mult (inv_pos (mpd_partition_temp Token vocab total_loss temperature temperature_pos prefix)
                               (mpd_partition_temp_pos Token vocab vocab_nonempty total_loss temperature temperature_pos prefix))
                      (mpd_minp_temp_sum_p mp2 prefix)))).
  - apply le_refl.
  - apply opp_le_compat. exact Hscaled.
Qed.

End ReqMpKernelWorld3.

(* mp 域收尾：6 件完成（对位裁决 1 + p 簇 5 件 + 定义   *)

(* 层对位全量在盘。                                              *)
(* ================= §2 rae_argmin_aux 族 ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* 引擎段 ReqArgminEngine：任意 (R,RIS) × 任意 Set 载体 A        *)
Section ReqArgminEngine.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable A : Set.
Variable key : A -> R.

(* 桥假设位 1：le 二分判定（RestB/MpDomain 位 1 同位） *)
Hypothesis rae_le_dec : forall a b : R, Or (le a b) (Not (le a b)).
(* 桥假设位 2：三分判定（仅 min 件 not_le 步使用） *)
Hypothesis rae_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* argmin 机器（mpd_argmin_aux_token 对位：key 打点化） *)
Fixpoint rae_argmin_aux (l : list A) (best : (A*R)%type) : (A*R)%type :=
  match l with
  | nil => best
  | a :: rest =>
      match rae_le_dec (key a) (snd best) with
      | inl _ => rae_argmin_aux rest (a, key a)
      | inr _ => rae_argmin_aux rest best
      end
  end.

(* InT 头前插（mpd_InT_head_extend 的任意 A 泛化） *)
Lemma rae_InT_head_extend : forall (x y a : A) (l : list A),
  InT x (y :: l) -> InT x (y :: a :: l).
Proof.
  intros x y a l H. inversion H; subst.
  - apply InT_here.
  - apply InT_next. apply InT_next. assumption.
Qed.

(* 1 min：And 两支遍历归纳（mpd_argmin_aux_token_min_mp 逐 tactic 同形；
   not_le 步以 rae_lt_dec 三分解：inl lt → lt_le_iff；mid req →
   le_id_l + le_refl；inr lt → 与 Hnot 相左而消空） *)
Lemma rae_argmin_aux_min : forall (l : list A) (best : (A*R)%type),
  And (forall w : A, InT w l ->
         le (snd (rae_argmin_aux l best)) (key w))
      (le (snd (rae_argmin_aux l best)) (snd best)).
Proof.
  induction l as [| a rest IH]; intro best.
  - assert (Hempty : forall w : A, InT w nil ->
      le (snd (rae_argmin_aux nil best)) (key w)).
    { intros w HIn. inversion HIn. }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (rae_le_dec (key a) (snd best)) as [Hle | Hnot].
    + destruct (IH (a, key a)) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (key a) _ IH_le Hle).
    + destruct (IH best) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- destruct (rae_lt_dec (snd best) (key a)) as [Hlt | [Heq | Hgt]].
           ++ exact (le_trans _ (snd best) _ IH_le (lt_le_iff _ _ (inl Hlt))).
           ++ exact (le_trans _ (snd best) _ IH_le
                       (le_id_l _ _ _ Heq (le_refl (key a)))).
           ++ exact (match Hnot (lt_le_iff _ _ (inl Hgt)) with end).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* 2 snd 恒等不变式（mpd_argmin_aux_token_snd_correct_mp 同形） *)
Lemma rae_argmin_aux_snd_correct : forall (l : list A) (best : (A*R)%type),
  snd best = key (fst best) ->
  snd (rae_argmin_aux l best) =
  key (fst (rae_argmin_aux l best)).
Proof.
  induction l as [| a rest IH]; intros best Hinit.
  - simpl. exact Hinit.
  - simpl.
    destruct (rae_le_dec (key a) (snd best)) as [Hle | Hnot].
    + exact (IH (a, key a) eq_refl).
    + exact (IH best Hinit).
Qed.

(* 遍历成员辅件（mpd_argmin_aux_token_mem 同形） *)
Lemma rae_argmin_aux_mem : forall (l : list A) (best : (A*R)%type),
  InT (fst (rae_argmin_aux l best)) (fst best :: l).
Proof.
  induction l as [| a rest IH]; intro best.
  - simpl. apply InT_here.
  - simpl. destruct (rae_le_dec (key a) (snd best)) as [Hle | Hnot].
    + apply InT_next. apply IH.
    + apply rae_InT_head_extend. apply IH.
Qed.

(* 挑选包装（mpd_pick_best_token 对位：nil → default） *)
Definition rae_pick (l : list A) (default : A) : A :=
  match l with
  | nil => default
  | a0 :: rest => fst (rae_argmin_aux rest (a0, key a0))
  end.

(* pick ∈ l（mpd_pick_best_in_vocab 对位：非空前提在载体侧） *)
Lemma rae_pick_mem : forall (l : list A) (default : A),
  Not (Id l nil) -> InT (rae_pick l default) l.
Proof.
  intros l default Hne. destruct l as [| a0 rest].
  - exact (match Hne (@id_refl (list A) nil) with end).
  - unfold rae_pick. apply (rae_argmin_aux_mem rest (a0, key a0)).
Qed.

(* 3 pick 最优性（mpd_pick_best_optimal_mp 对位；1+2 组装；
   snd 恒等伴件以 eq_rect 纯 term 运输，零目标换形战术） *)
Theorem rae_pick_optimal : forall (l : list A) (default : A) (w : A),
  InT w l -> le (key (rae_pick l default)) (key w).
Proof.
  intros l default w Hw. unfold rae_pick.
  destruct l as [| a0 rest].
  - inversion Hw.
  - destruct (rae_argmin_aux_min rest (a0, key a0)) as [Hmin Hle].
    assert (Hsnd : snd (rae_argmin_aux rest (a0, key a0)) =
                   key (fst (rae_argmin_aux rest (a0, key a0))))
      by exact (rae_argmin_aux_snd_correct rest (a0, key a0) eq_refl).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + exact (eq_rect (snd (rae_argmin_aux rest (a0, key a0)))
               (fun r => le r (key a0)) Hle
               (key (fst (rae_argmin_aux rest (a0, key a0))))
               Hsnd).
    + exact (eq_rect (snd (rae_argmin_aux rest (a0, key a0)))
               (fun r => le r (key w)) (Hmin w Hwrest)
               (key (fst (rae_argmin_aux rest (a0, key a0))))
               Hsnd).
Qed.

End ReqArgminEngine.

(* 复原验证段 MpRecycleProbe：mp 域 argmin = 引擎实例            *)
(*（位形 = UpReqMpDomain Section ReqMpKernelWorld2 中 argmin 机器  *)
(*  实际使用的假设位：Token / total_loss / 判定位 1+2；其余节变量    *)
(*  vocab_nonempty/temperature/default_token/min_p 不入机器闭包） *)
Section MpRecycleProbe.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.
Variable total_loss : list Token -> R.
Hypothesis probe_le_dec : forall a b : R, Or (le a b) (Not (le a b)).
Hypothesis probe_lt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* mp 专用腿①：key 函数 = total_loss (prefix ++ [w]) *)
Definition mp_key (prefix : list Token) : Token -> R :=
  fun w => total_loss (prefix ++ [w]).

(* 定义级 transport：mp 域 argmin 机器与引擎实例逐点相等（归纳 +
   转换级：mp 机器递归多穿 prefix 参、引擎打点化 key，二者在
   A:=Token, key:=mp_key prefix 假设位下逐支同形——复原结论的转换级
   证据：mp 机器就是引擎的特例） *)
Lemma mpd_argmin_engine_transport : forall (prefix l : list Token)
         (best : (Token*R)%type),
  mpd_argmin_aux_token Token total_loss probe_le_dec prefix l best =
  @rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec l best.
Proof.
  intros prefix l. induction l as [| a rest IH]; intro best.
  - reflexivity.
  - simpl. unfold mp_key.
    destruct (probe_le_dec (total_loss (prefix ++ [a])) (snd best))
      as [Hc | Hc].
    + exact (IH (a, mp_key prefix a)).
    + exact (IH best).
Qed.

(* 挑选包装 transport（vocab/default 腿②：nil → default 同位） *)
Lemma mpd_pick_engine_transport : forall (vocab : list Token)
         (default_token : Token) (prefix : list Token),
  mpd_pick_best_token Token vocab total_loss default_token probe_le_dec prefix =
  @rae_pick R RIS Token (mp_key prefix) probe_le_dec vocab default_token.
Proof.
  intros vocab default_token prefix.
  destruct vocab as [| w0 rest].
  - reflexivity.
  - unfold mpd_pick_best_token, rae_pick. f_equal.
    exact (mpd_argmin_engine_transport prefix rest
             (w0, total_loss (prefix ++ [w0]))).
Qed.

(* mp 域件 1 由引擎直供（语句与 mpd_argmin_aux_token_min_mp 消解形同位，
   核心转换级闭合：transport + mp_key δ/β） *)
Theorem mpd_argmin_aux_token_min_via_engine : forall (prefix l : list Token)
         (best_token : Token) (best_loss : R),
  And (forall w : Token, InT w l ->
         le (snd (mpd_argmin_aux_token Token total_loss probe_le_dec
                    prefix l (best_token, best_loss)))
            (total_loss (prefix ++ [w])))
      (le (snd (mpd_argmin_aux_token Token total_loss probe_le_dec
                 prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l best_token best_loss.
  destruct (@rae_argmin_aux_min R RIS Token (mp_key prefix)
              probe_le_dec probe_lt_dec l (best_token, best_loss))
    as [Hmin Hle].
  assert (T : mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss) =
              @rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                l (best_token, best_loss))
    by exact (mpd_argmin_engine_transport prefix l (best_token, best_loss)).
  split.
  - intros w Hw.
    exact (eq_rect (@rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                      l (best_token, best_loss))
             (fun z => le (snd z) (mp_key prefix w)) (Hmin w Hw)
             (mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss))
             (eq_sym T)).
  - exact (eq_rect (@rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                      l (best_token, best_loss))
             (fun z => le (snd z) (snd (best_token, best_loss))) Hle
             (mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss))
             (eq_sym T)).
Qed.

(* mp 域件 2 由引擎直供（snd 恒等不变式） *)
Theorem mpd_argmin_aux_token_snd_correct_via_engine :
  forall (prefix l : list Token) (best_token : Token) (best_loss : R),
  best_loss = total_loss (prefix ++ [best_token]) ->
  snd (mpd_argmin_aux_token Token total_loss probe_le_dec
         prefix l (best_token, best_loss)) =
  total_loss (prefix ++
    [fst (mpd_argmin_aux_token Token total_loss probe_le_dec
            prefix l (best_token, best_loss))]).
Proof.
  intros prefix l best_token best_loss Hinit.
  assert (T : mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss) =
              @rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                l (best_token, best_loss))
    by exact (mpd_argmin_engine_transport prefix l (best_token, best_loss)).
  exact (eq_rect (@rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                    l (best_token, best_loss))
           (fun z => snd z = total_loss (prefix ++ [fst z]))
           (@rae_argmin_aux_snd_correct R RIS Token (mp_key prefix)
              probe_le_dec l (best_token, best_loss) Hinit)
           (mpd_argmin_aux_token Token total_loss probe_le_dec
              prefix l (best_token, best_loss))
           (eq_sym T)).
Qed.

(* mp 域遍历成员件由引擎直供 *)
Theorem mpd_argmin_aux_token_mem_via_engine :
  forall (prefix l : list Token) (best_token : Token) (best_loss : R),
  InT (fst (mpd_argmin_aux_token Token total_loss probe_le_dec
              prefix l (best_token, best_loss)))
      (best_token :: l).
Proof.
  intros prefix l best_token best_loss.
  assert (T : mpd_argmin_aux_token Token total_loss probe_le_dec
                prefix l (best_token, best_loss) =
              @rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                l (best_token, best_loss))
    by exact (mpd_argmin_engine_transport prefix l (best_token, best_loss)).
  exact (eq_rect (@rae_argmin_aux R RIS Token (mp_key prefix) probe_le_dec
                    l (best_token, best_loss))
           (fun z => InT (fst z) (best_token :: l))
           (@rae_argmin_aux_mem R RIS Token (mp_key prefix)
              probe_le_dec l (best_token, best_loss))
           (mpd_argmin_aux_token Token total_loss probe_le_dec
              prefix l (best_token, best_loss))
           (eq_sym T)).
Qed.

(* mp 域件 3（pick 最优性）由引擎直供（腿①②经 transport 换算） *)
Theorem mpd_pick_best_optimal_via_engine :
  forall (vocab : list Token) (default_token : Token)
         (prefix : list Token) (w : Token),
  InT w vocab ->
  le (total_loss (prefix ++
        [mpd_pick_best_token Token vocab total_loss default_token
                             probe_le_dec prefix]))
     (total_loss (prefix ++ [w])).
Proof.
  intros vocab default_token prefix w Hw.
  assert (PT : mpd_pick_best_token Token vocab total_loss default_token
                 probe_le_dec prefix =
               @rae_pick R RIS Token (mp_key prefix) probe_le_dec
                 vocab default_token)
    by exact (mpd_pick_engine_transport vocab default_token prefix).
  exact (eq_rect (@rae_pick R RIS Token (mp_key prefix) probe_le_dec
                    vocab default_token)
           (fun z => le (total_loss (prefix ++ [z]))
                        (total_loss (prefix ++ [w])))
           (@rae_pick_optimal R RIS Token (mp_key prefix) probe_le_dec
              probe_lt_dec vocab default_token w Hw)
           (mpd_pick_best_token Token vocab total_loss default_token
              probe_le_dec prefix)
           (eq_sym PT)).
Qed.

End MpRecycleProbe.
(* ================= §2 traj_table 族 ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.
Open Scope Q_scope.

(* 段1：下降轨迹有限采样表（B 件链侧，Q 载体）                     *)

(* 采样表 traj_table h t x n = [x; step x; …; stepⁿ x]，
   第 i 项 = sf_grad_descent h t x i（n+1 个点）。 *)
Fixpoint traj_table (h t x : Q) (n : nat) : list Q :=
  match n with
  | O => x :: nil
  | Datatypes.S n' => x :: traj_table h t (sf_grad_step h t x) n'
  end.

Lemma head_InT_traj_table : forall (h t x : Q) (n : nat),
  InT x (traj_table h t x n).
Proof.
  intros h t x n. revert x. induction n as [| n' IH]; intros x; cbn [traj_table].
  - apply InT_here.
  - apply InT_here.
Qed.

(* 表非空（nil 支配案经构造子失配 inversion 闭合——引擎件同位先例） *)
Lemma traj_table_nonempty : forall (h t x : Q) (n : nat),
  Not (Id (traj_table h t x n) nil).
Proof.
  intros h t x n. revert t x. induction n as [| n' IH]; intros t x Hnil;
    cbn [traj_table] in Hnil.
  - inversion Hnil.
  - inversion Hnil.
Qed.

(* 遍历件：第 j 个迭代点必在表中（j ≤ n）——主件 (a) 面的轨迹具体化 *)
Lemma traj_table_iterate_mem : forall (h t x : Q) (n j : nat),
  (j <= n)%nat -> InT (sf_grad_descent h t x j) (traj_table h t x n).
Proof.
  intros h t x n. revert x. induction n as [| n' IH]; intros x j Hj.
  - assert (E : j = 0%nat) by lia.
    rewrite E. cbn [sf_grad_descent traj_table]. apply InT_here.
  - revert Hj. destruct j as [| j']; intros Hj.
    + cbn [sf_grad_descent traj_table]. apply InT_here.
    + cbn [sf_grad_descent traj_table]. apply InT_next.
      apply IH. lia.
Qed.

(* ε-传递件（Q 层）：u ≤ v ∧ 0 ≤ eps ⟹ u ≤ v + eps（QleT' 出口） *)
Lemma qlep_add_eps : forall (u v eps : Q),
  QleT' u v -> QleT' 0 eps -> QleT' u (v + eps).
Proof.
  intros u v eps Huv Heps.
  apply Qle_to_QleT'.
  apply (Qle_trans u v (v + eps)).
  - apply QleT'_to_Qle. exact Huv.
  - apply (Qle_trans v (v + 0) (v + eps)).
    + apply sf_qeq_le. exact (Qeq_sym (v + 0) v (Qplus_0_r v)).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle. exact Heps.
Qed.

(* 段2：抽象 argmin ε-最优见证（A 件引擎侧）                       *)
Section EpsOptimalReachCore.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable A : Set.
Variable key : A -> R.
(* 桥假设位 1+2（UpReqArgminEngine Section 同位：le 二分 / 三分判定） *)
Hypothesis hle_dec : forall a b : R, Or (le a b) (Not (le a b)).
Hypothesis hlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)).

(* 支撑件 ε-松化：支配 u ≤ v 加 eps ≥ 0 ⟹ ε-支配 u ≤ v + eps。
   装配：le_trans × (req→le 经 lt_le_iff 右支) × le_plus_compat。 *)
Lemma eps_loosen : forall (u v eps : R),
  le u v -> le zero eps -> le u (plus v eps).
Proof.
  intros u v eps Huv Heps.
  apply (le_trans u v (plus v eps)).
  - exact Huv.
  - apply (le_trans v (plus v zero) (plus v eps)).
    + apply lt_le_iff. apply inr.
      exact (req_sym (plus v zero) v (plus_zero v)).
    + apply le_plus_compat.
      * apply le_refl.
      * exact Heps.
Qed.

(* ε-最优可达见证形（Set 层 sigT 封装：成员 + 支配 + ε-支配） *)
Definition optimal_pick_witness (l : list A) (default : A) (eps : R) : Set :=
  sigT (fun xstar =>
    And (InT xstar l)
        (And (forall w : A, InT w l -> le (key xstar) (key w))
             (forall w : A, InT w l -> le (key xstar) (plus (key w) eps)))).

(* 主件：任意有限非空表 + 任意非负比较阈 eps ⟹ argmin 点的
   支配/逼近 sigT 见证。证书由 A 件引擎直供：
   成员 = rae_pick_mem，支配 = rae_pick_optimal，ε-形 = eps_loosen。 *)
Theorem finite_table_eps_optimal_witness :
  forall (l : list A) (default : A) (eps : R),
    Not (Id l nil) -> le zero eps ->
    optimal_pick_witness l default eps.
Proof.
  intros l default eps Hne Heps.
  refine (existT _ (rae_pick A key hle_dec l default) _).
  split.
  - exact (@rae_pick_mem R RIS A key hle_dec l default Hne).
  - split.
    + intros w Hw.
      exact (@rae_pick_optimal R RIS A key hle_dec hlt_dec l default w Hw).
    + intros w Hw.
      exact (eps_loosen (key (rae_pick A key hle_dec l default)) (key w) eps
               (@rae_pick_optimal R RIS A key hle_dec hlt_dec l default w Hw)
               Heps).
Qed.

End EpsOptimalReachCore.

(* 段3：合成——有限轨迹上的 ε-最优可达 + quad_cost 一档对接         *)

(* 合成主件：下降轨迹采样表上的 ε-最优可达见证。
   A := Q（B 件轨迹点载体），key 抽象（任意代价函数），
   支配证书由段2 主件在 l := traj_table h t x0 n 接口参数实例化。
   出口：sigT + And + InT + RIS le，零 Prop 语句面。 *)
Theorem trajectory_eps_optimal_reach :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (keyQ : Q -> R)
         (hle_dec : forall a b : R, Or (le a b) (Not (le a b)))
         (hlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a)))
         (h t x0 : Q) (eps : R) (n : nat),
    le zero eps ->
    sigT (fun xstar =>
      And (InT xstar (traj_table h t x0 n))
          (And (forall w : Q, InT w (traj_table h t x0 n)
                             -> le (keyQ xstar) (keyQ w))
               (forall w : Q, InT w (traj_table h t x0 n)
                             -> le (keyQ xstar) (plus (keyQ w) eps)))).
Proof.
  intros R RIS keyQ hle_dec hlt_dec h t x0 eps n Heps.
  exact (@finite_table_eps_optimal_witness R RIS Q keyQ hle_dec hlt_dec           (traj_table h t x0 n) x0 eps           (traj_table_nonempty h t x0 n) Heps).
Qed.

(* B 件对接（一档）：n 步下降终点的 ε-上界。
   sf_grad_descent_convergence（QleT' 精确收缩界）+ qlep_add_eps 松化。
   注：Q 无 RIS 实例（见头注），故 Q 层 key 实例化走 QleT' 链。 *)
Theorem quad_cost_descent_eps_bound :
  forall (h t x0 eps : Q) (n : nat),
    QltT 0 h -> QltT h 2 -> QleT' 0 eps ->
    QleT' (sf_quad_cost t (sf_grad_descent h t x0 n))
          (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x0 + eps).
Proof.
  intros h t x0 eps n Hh H2 Heps.
  exact (qlep_add_eps (sf_quad_cost t (sf_grad_descent h t x0 n))           (qpow2 ((1 - h) * (1 - h)) n * sf_quad_cost t x0) eps           (sf_grad_descent_convergence h t x0 n Hh H2) Heps).
Qed.

(* 审查留痕面：G4（≥1 语句） *)
Print Assumptions finite_table_eps_optimal_witness.
Print Assumptions trajectory_eps_optimal_reach.
Print Assumptions quad_cost_descent_eps_bound.
Print Assumptions traj_table_iterate_mem.
