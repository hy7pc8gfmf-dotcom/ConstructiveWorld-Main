(* UpReqMpDomain.v — 席X3：mp 域 req 层引擎与首批实例（20260911）
   ----------------------------------------------------------------
   冻结判词（迁移总账 mp 域 9 件 + inv_vocab 2 件 + attn_nat_to_R_pos 1 件，
   共 12 件）立论 =「mp 嵌入域跨接口不可复用（缺 nat→req-R 桥）」。
   席N2 实证该前提已消失：上游引擎 reqd_of_nat（UpReqDist.v L286，ReqGRPO
   节闭合后导出的 nat→req-R 嵌入）+ rsum/rls_* 求和桥（UpReqAlignRestB.v
   Part 0）+ 单调件（UpReqAlgebra req_mult_plus_distr_r / req_le_mult_compat_r
   等）全部在盘。本件补 nat→req-R 桥的正性/步进公共件 + 首批实例。

   母本：S06_DiffSamplingGibbs.v Section MinPSampling T2.4-2 节
   （= CW219 大库 L31545-31834；总账 L602-612 冻结名单）。
   ----------------------------------------------------------------
   逐件对位台账（req 件名 <- Id 原件 @ 原件分片行号 / 总账行号）：
   [引擎段 ReqMpEngineNum]
     E1 reqd_of_nat_succ（定义性：reqd_of_nat (S n) ≡ 1 + reqd_of_nat n）
     E2 reqd_of_nat_pos（nat 归纳正性）＝ attn_nat_to_R_pos 对位
        （S13_NLiveAudit.v L2301 / 总账 L113：attn_nat_to_R 与 reqd_of_nat
        为同一 Fixpoint 形 O↦zero, S n↦1+·；req 对位以共享嵌入 reqd_of_nat
        陈述，语句逐字同形 lt zero (· (S k))）
     E3 req_le_one_mult_le_inv_mp <- le_one_mult_le_inv_mp
        （S06 L7061 / 总账 L618；纯代数：1 ≤ G·M ⟹ inv G ≤ M）
   [实例段 ReqMpNatDomain]
     I1 reqd_mp_of_nat_pos <- mp_of_nat_pos（S06 L6893 / 总账 L602）
     I2 req_rsum_le_const_mp <- list_sum_le_const_mp
        （S06 L7027 / 总账 L617；兼作滚动席链① minp_max_ge_inv_vocab_size
        的核心腿：Σ f l ≤ of_nat(|l|)·M）
   [实例段 ReqMpKernelWorld]
     I3 req_markov_kernel_normalized_mp <- markov_kernel_normalized_mp
        （S06 L6913 / 总账 L603；mpd_* 定义族与基座 temp_factor/
        partition_temp/markov_kernel 逐位同形——RestB alb_* 闭包显式参数
        先例，原证明 Hext/Hlin/Hp 三步逐位对位）
     I4 req_temp_factor_antitone_mp <- temp_factor_antitone_mp
        （S06 L6943 / 总账 L604；exp_neg_le_decr + 正因子左乘保序）
   ----------------------------------------------------------------
   余件清单（本席不做，滚动席续作；逐件依赖注记见文件尾）：
     argmin_aux_token_min_mp（S06 L6976）/ argmin_aux_token_snd_correct_mp
     （S06 L7024）/ pick_best_optimal_mp（S06 L7044）/ markov_kernel_le_max_mp
     （S06 L7066）/ minp_max_ge_inv_vocab_size（S06 L7082）/ 
     minp_dropped_mass_le_inv_vocab_size（S06 L7097）——argmin/list-Id 机器
     3 件 + 组装 3 件（依赖 I2 + I3 + E3 桥件，引擎已备）。
   ----------------------------------------------------------------
   纪律：纯构造性；Set 层语句（req/lt/le 接口 Set 值；Or/And/Id(list/nat)/
   Not 按 UpKVEv/RestB 先例）；纯 term/结构化 apply（req_trans 链 + compat
   桥），零 rewrite、零未闭合证明；核心件 Qed。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqDist.
Require Import UpReqAlignRestB.
Require Import UpReqAlgebra.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 引擎段 ReqMpEngineNum：nat→req-R 嵌入（reqd_of_nat）公共桥件  *)
(* ============================================================ *)
Section ReqMpEngineNum.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* E1 步进桥：reqd_of_nat (S n) 与 1 + reqd_of_nat n 逐点 δ 相等 *)
Lemma reqd_of_nat_succ : forall n : nat,
  req (reqd_of_nat (Datatypes.S n)) (plus one (reqd_of_nat n)).
Proof.
  intro n. apply req_refl.
Qed.

(* E2 嵌入正性＝attn_nat_to_R_pos 对位（S13 L2301）：0 < reqd_of_nat (S k)。
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

(* E3 <- le_one_mult_le_inv_mp（S06 L7061 / 总账 L618）：
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

(* ============================================================ *)
(* 实例段 ReqMpNatDomain：nat 计数域两件（I1 / I2）              *)
(* ============================================================ *)
Section ReqMpNatDomain.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.

(* I1 <- mp_of_nat_pos（S06 L6893 / 总账 L602）：
   l ≠ nil ⟹ 0 < of_nat(|l|)。嵌入统一为 reqd_of_nat（总账判词之
   「缺 nat→req-R 桥」即由本件消除）；长度非空 ⟹ 形如 S k，归 E2。 *)
Lemma reqd_mp_of_nat_pos : forall l : list Token,
  Not (Id l nil) -> lt zero (reqd_of_nat (length l)).
Proof.
  intros l Hl. destruct l as [| w rest].
  - exact (match Hl (@id_refl (list Token) nil) with end).
  - simpl. exact (reqd_of_nat_pos (length rest)).
Qed.

(* I2 <- list_sum_le_const_mp（S06 L7027 / 总账 L617）：
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

(* ============================================================ *)
(* 实例段 ReqMpKernelWorld：Min-P 核域（I3 / I4）                *)
(*   接口假设与基座 MinPSampling L5934-5945 同位（Token/vocab/   *)
(*   total_loss/temperature 六参闭包）；mpd_* 定义族 δ 透明同形  *)
(*   于 RestB alb_temp_factor/alb_partition_temp/alb_markov_     *)
(*   kernel（闭包显式参数先例）。                                *)
(* ============================================================ *)
Section ReqMpKernelWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
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

(* I3 <- markov_kernel_normalized_mp（S06 L6913 / 总账 L603）：
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

(* I4 <- temp_factor_antitone_mp（S06 L6943 / 总账 L604）：
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

(* ============================================================ *)
(* 文件尾：余件清单（滚动席续作，总账 L605-612 未清部分）        *)
(* ------------------------------------------------------------
   1. argmin_aux_token_min_mp（S06 L6976 / 总账 L605）：
      argmin 遍历最小性——ord_le_dec 换 req_le_dec 桥假设（RestB
      T2① 同位），le_refl/le_trans 接口字段直换；InT 解构保持
      Id 层（list 机器不迁，§1.1 边界 2）。难度：中。
   2. argmin_aux_token_snd_correct_mp（S06 L7024 / 总账 L606）：
      snd 恒等不变式——纯 Id 层归纳（中支判定换 req_le_dec），
      语句 Id 等式保持（best_loss = ... 为 Id）。难度：低-中。
   3. pick_best_optimal_mp（S06 L7044 / 总账 L607）：
      pick_best 最优性——依赖 1+2 + vocab 解构；难度：中。
   4. markov_kernel_le_max_mp（S06 L7066 / 总账 L608）：
      kernel w ≤ max——依赖 3 + I4（temp_factor_antitone）+
      le_mult_compat 弱形（接口字段在盘）；难度：低（引擎齐备）。
   5. minp_max_ge_inv_vocab_size（S06 L7082 / 总账 L611，链①）：
      1 == Σkernel（I3）≤ |S|·max（I2 实例）⟹ inv(|S|) ≤ max
      （E3）；链式组装，Id/req 等式桥按 RestB 归一化定理同形。
      难度：中（三腿全在盘）。
   6. minp_dropped_mass_le_inv_vocab_size（S06 L7097 / 总账 L612，
      链②）：dropped ≤ 1 − p_max（RestB req_minp_dropped_mass_le_
      one_minus_max 已在盘）+ 链① + opp_le_compat 组装；难度：中。
   附：argmin_aux_token / pick_best_token / max_markov_prob 三定义
   的 req 节内对位定义（RestB alb_max_markov_prob 已有 max 同位；
   argmin 需新建，建议并入滚动席 ReqMpKernelWorld 续节）。
   ============================================================ *)
(* ============================================================ *)
(* 席X3b2 续作（20260911）：mp 域余 6 件全清（argmin 簇 3 + 组装 3） *)
(* ------------------------------------------------------------
   台账（req 件名 <- Id 原件 @ S06 行号 / 总账行号）：
     1 mpd_argmin_aux_token_min_mp <- argmin_aux_token_min_mp
        （S06 L6976 / 总账 L605；判定换 req_le_dec 桥假设位 1；
        原件 not_le_lt 步（S01 判定序域字段，req 域无同名字段）以
        桥假设位 2 req_lt_dec 三分解替之——RestB ReqSamplingWorld
        桥假设位 2 同位；le_refl/le_trans/le_id_l 接口字段直换）
     2 mpd_argmin_aux_token_snd_correct_mp <- S06 L7024 / 总账 L606
        （纯 Id 层归纳，中支判定换 req_le_dec；语句 Id 等式保持）
     3 mpd_pick_best_optimal_mp <- S06 L7044 / 总账 L607
        （依赖 1+2 + vocab 解构；snd 恒等以 Id 层 rewrite 运输，
        list-Id 机器不迁边界内）
     4 mpd_markov_kernel_le_max_mp <- S06 L7066 / 总账 L608
        （le_mult_compat_weak 接口字段直用 + I4 req_temp_factor_
        antitone_mp + 件 3）
     5 mpd_minp_max_ge_inv_vocab_size <- S06 L7082 / 总账 L611 链①
        （I3 归一化 + I2 req_rsum_le_const_mp + E3 req_le_one_mult_
        le_inv_mp 三腿组装；mp_of_nat → reqd_of_nat 桥）
     6 mpd_minp_dropped_mass_le_inv_vocab_size <- S06 L7097 /
        总账 L612 链②（dropped ≤ 1−max 腿按 RestB req_minp_dropped_
        mass_le_one_minus_max 同证形移植（alb_→mpd_ 逐位改名），+
        链① + opp_le_compat 组装）
   定义簇（S06 L6044-6061/L6167-6171/L6174-6191/L6504 对位；
   RestB alb_ 闭包显式参数先例，mpd_markov_kernel 等首批 discharged
   定义以全闭包显式消费）：
     mpd_argmin_aux_token / mpd_pick_best_token（default_token 参，
     S06 L5946 同位）/ mpd_pick_max_token / mpd_max_markov_prob /
     mpd_minp_threshold / mpd_minp_keep / mpd_minp_keep_dec /
     mpd_minp_temp_sum / mpd_minp_dropped_mass
   桥假设：位 1 req_le_dec（RestB 位 1 同位）；位 2 req_lt_dec
   （RestB 位 2 同位，本席兼作 S06 not_le_lt 步替代腿）。
   ============================================================ *)
Section ReqMpKernelWorld2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable Token : Set.
Variable vocab : list Token.
Variable vocab_nonempty : Not (Id vocab nil).
Variable total_loss : list Token -> R.
Variable temperature : R.
Variable temperature_pos : lt zero temperature.
Variable default_token : Token.
Variable min_p : R.
Variable min_p_lt_one : lt min_p one.

(* 桥假设位 1：DecidableOrder ord_le_dec（S01 L331 同位）的 req 镜像 *)
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

(* 1 <- argmin_aux_token_min_mp（S06 L6976 / 总账 L605）：
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

(* 2 <- argmin_aux_token_snd_correct_mp（S06 L7024 / 总账 L606）：
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

(* 3 <- pick_best_optimal_mp（S06 L7044 / 总账 L607）：
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

(* ---- 定义簇 2：max（S06 L6167-6171 对位；首批 discharged 定义全闭包消费） ---- *)
Definition mpd_pick_max_token (prefix : list Token) : Token := mpd_pick_best_token prefix.

Definition mpd_max_markov_prob (prefix : list Token) : R :=
  mpd_markov_kernel Token vocab vocab_nonempty total_loss temperature temperature_pos prefix
                    (mpd_pick_max_token prefix).

(* 4 <- markov_kernel_le_max_mp（S06 L7066 / 总账 L608）：
   le_mult_compat_weak 接口字段（le zero c → le a b → le a·c ≤ b·c）
   直用；单调腿 = I4 + 件 3。 *)
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

(* 5 <- minp_max_ge_inv_vocab_size（S06 L7082 / 总账 L611，链①）：
   inv(|S|) ≤ max。三腿：I3 归一化（Σkernel == 1）+ I2 逐项和界
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

(* 6 <- minp_dropped_mass_le_inv_vocab_size（S06 L7097 / 总账 L612，链②）：
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

(* ============================================================ *)
(* 席X3b2 收尾：12 件全清（首批 8 decl + 本批 6 件 + 辅件）。      *)
(* 文件尾原余件清单（上文）由本节全数闭合，特此注记。            *)
(* ============================================================ *)
