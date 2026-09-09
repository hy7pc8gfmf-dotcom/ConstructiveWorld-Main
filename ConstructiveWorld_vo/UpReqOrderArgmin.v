(* UpReqOrderArgmin.v — 签名迁移批 5 波 4 桥席 C1：reqDecidableOrder 同构假设类
   + reqArgmin 归纳机 + argmin 簇 (c) 5 件 req 平移。
   工作单：attn\批5基建层处置清单-20260909.md 波4/(c) 桥C1（§0.3 / §7.3 / §7.9 / §8 / §9.2）。
   母本：CW_ConstructiveWorld_219：
     Class DecidableOrder          L331-337（字段面 5 槽，: Set）
     Section ArgminCorrectness     L15288-15425（argmin_aux 系；节参数 Context {DO} L15290）
     SLM argmin 子节               L2426-2560（argmin_aux_token 系；Context {DO} L2426）
   上游：CW219 基座（RealInterfaceEnhancedSetoid 接口字段直引：le/lt/req/le_trans/
   le_refl/lt_le_iff/req_le_compat）；UpReqAlgebra 按需——argmin 簇字段面全在基座
   接口，本件未消费故未 Require。在飞 5 件（UpReqSLM/UpReqCauchy/UpReqMisc5/
   UpEntropyGainReq/UpReqAlign3）零 Require（工作单红线）；假设位组同类文字对齐自持。
   ----------------------------------------------------------------
   桥设计（T2①：Class 槽位非公理——reqDecidableOrder 为 Class 定义，消费节以
   Context {DO : reqDecidableOrder R RIS} 引入，End 时作显式参入闭包签名，
   Print Assumptions 仍 Closed。E225 判词：DecidableOrder=整体三分律=LPO 等价、
   全库零 Instance——req 类同为永久假设类，不供 Instance，与 Id 同构）。
   字段面逐字段对账（Id L331-337 → 本类；等词位 Id→req）：
     ord_le_dec    L332  Or (le a b) (Not (le a b))    → rord_le_dec    （逐字同形）
     lt_dec        L333  Or (lt a b) (Or (Id a b) ..) → rlt_dec        （中支 Id→req；
                                          RestB req_lt_dec L446 同款签名差异台账）
     eq_dec        L334  Or (Id a b) (Not (Id a b))   → rreq_dec       （Id→req）
     not_le_lt     L335  Not (le a b) -> lt b a       → rnot_le_lt     （逐字同形）
     lt_le_iff_dec L336  Or (lt a b) (Id a b) -> le   → rlt_le_iff_dec （Id→req；
                                          req 形即接口字段 lt_le_iff 同语句）
   ----------------------------------------------------------------
   交付对账（清单 (c) 5 件，行号逐件在表）：
     req_argmin_aux_token_min             ← argmin_aux_token_min        L2481（SLM §7.3）
     req_pick_best_token_optimal          ← pick_best_optimal           L2545（SLM §7.3）
     req_argmin_aux_correct               ← argmin_aux_correct          L15315（Argmin §7.9）
     req_pick_best_is_minimal             ← pick_best_is_minimal        L15377（Argmin §7.9）
     req_dynamics_greedy_locally_optimal  ← dynamics_greedy_locally_optimal L15407（§7.9）
   机器 2 枚（清单 L144/L315 判词「随桥C1 立项可转定义级 (b)」兑现——snd 伴件
   的 req 等词改述版归纳机，零 Leibniz 面逐字：Id 系逐处 Hsnd 等词换形 → req 系
   沿接口 Proper 字段 req_le_compat 运输 le 语句，纯 term）：
     req_argmin_aux_token_snd_req         ← argmin_aux_token_snd_correct L2517（改述）
     req_argmin_aux_snd_req               ← argmin_aux_snd_correct       L15352（改述）
   ----------------------------------------------------------------
   (d) 冻结清单（零证明行，见文件尾注记）：InT_head_extend L2451 /
   argmin_aux_token_mem L2461 / argmin_aux_token_snd_correct L2517（Id 形不迁，
   req 形机已转 (b) 入上表）/ pick_best_in_vocab' L2531 / pick_best_in_vocab L2575 /
   argmin_aux_snd_correct L15352（同前）。
   纪律：纯构造性；Set 层语句（le/lt/req/Or/And 全基座 Set 形连接词 L65-70）；
   纯 term-mode（apply/exact/destruct/inversion/specialize/unfold），零依赖改写器；
   核心件 Qed。G3 提取探针独立文件（验后删）。 *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 桥 C1 本体 1：reqDecidableOrder——Id DecidableOrder L331-337     *)
(*   的 req 同构假设类（T2① Class 槽位非公理；全库零 Instance      *)
(*   与 Id 同判——E225 LPO 判词随桥注记）                          *)
(* ============================================================ *)
Class reqDecidableOrder (R : Set) (RIS : RealInterfaceEnhancedSetoid R) : Set := {
  rord_le_dec : forall a b : R, Or (le a b) (Not (le a b));
  rlt_dec : forall a b : R, Or (lt a b) (Or (req a b) (lt b a));
  rreq_dec : forall a b : R, Or (req a b) (Not (req a b));
  rnot_le_lt : forall a b : R, Not (le a b) -> lt b a;
  rlt_le_iff_dec : forall a b : R, Or (lt a b) (req a b) -> le a b
}.

(* ============================================================ *)
(* reqArgmin 机·SLM 支（基座 SLM argmin 子节 L2426-2560 同构；      *)
(*   只建 (c) 2 件与消费面机器，(d) 5 件冻结承接不触及）            *)
(* ============================================================ *)
Section ReqArgminTokenWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {DO : reqDecidableOrder R RIS}.

(* ---- 接口假设（L2035 区同构子集：本 2 件消费面，vocab_nonempty
     不入——pick_best 系两件零消费，诚实边界注记） ---- *)
Variable Token : Set.
Variable vocab : list Token.
Variable total_loss : list Token -> R.
Variable default_token : Token.

(* 基座 candidate_token L2432 同形 *)
Definition req_candidate_token : Set := (Token * R)%type.

(* 基座 argmin_aux_token L2434-2444 同形（判定槽 = rord_le_dec） *)
Fixpoint req_argmin_aux_token (prefix : list Token) (l : list Token)
         (best : req_candidate_token) : req_candidate_token :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match rord_le_dec loss_w (snd best) with
      | inl _ => req_argmin_aux_token prefix rest (w, loss_w)
      | inr _ => req_argmin_aux_token prefix rest best
      end
  end.

(* 基座 pick_best_token L2446-2452 同形 *)
Definition req_pick_best_token (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (req_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* 基座 argmin_aux_token_min L2481（(c) 件 1）：遍历正确性——snd 不增
   （第二分量）+ 对 l 内逐项最小（第一分量）。归纳 + rord_le_dec 分支 +
   rnot_le_lt/lt_le_iff 反向支，逐位镜像 Id 机。 *)
Lemma req_argmin_aux_token_min : forall prefix l best_token best_loss,
  And (forall w : Token, InT w l ->
    le (snd (req_argmin_aux_token prefix l (best_token, best_loss)))
       (total_loss (prefix ++ [w])))
      (le (snd (req_argmin_aux_token prefix l (best_token, best_loss))) best_loss).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - (* nil：左分量空域真 + le_refl（空支以 inversion 收口——提取零 Obj.magic，
       E-STAGING-MinP 行 101 同坑：空支 match 字面会落 Obj.magic） *)
    assert (Hempty : forall w : Token, InT w nil ->
      le (snd (req_argmin_aux_token prefix nil (best_token, best_loss)))
         (total_loss (prefix ++ [w]))).
    { intros w HIn. inversion HIn. }
    exact (pair Hempty (le_refl _)).
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + (* 换 a：IH 于新 best (a, loss a)；snd ≤ loss a（IH 左腿），传 le_trans 配 Hle *)
      destruct (IH a (total_loss (prefix ++ [a]))) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
    + (* 保留 best：rnot_le_lt 升严格序 + lt_le_iff 回 le；逐项走 IH *)
      destruct (IH best_token best_loss) as [IH_min IH_le].
      split.
      * intros w HIn. inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a])))
             by exact (rnot_le_lt (total_loss (prefix ++ [a])) best_loss Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
      * exact IH_le.
Qed.

(* 机器：基座 argmin_aux_token_snd_correct L2517 的 req 等词改述版（清单 L144
   「随桥C1 立项可转定义级 (b)」兑现）。基例与归纳步全为转换级：req_argmin_aux
   的递归分支两侧 fst/snd 同源， premise req 等词沿归纳原样传——零 Leibniz 面。 *)
Lemma req_argmin_aux_token_snd_req : forall prefix l best_token best_loss,
  req best_loss (total_loss (prefix ++ [best_token])) ->
  req (snd (req_argmin_aux_token prefix l (best_token, best_loss)))
      (total_loss (prefix ++ [fst (req_argmin_aux_token prefix l (best_token, best_loss))])).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - exact Hinit.
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) (req_refl _)).
    + exact (IH best_token best_loss Hinit).
Qed.

(* 基座 pick_best_optimal L2545（(c) 件 2）：pick_best 扩展损失 ≤ 任意
   w ∈ vocab 的。Id 系逐处 Leibniz Hsnd 换形 → req 系 req_le_compat（接口
   Proper 字段）沿 req 等词运输 le 语句，纯 term。 *)
Theorem req_pick_best_token_optimal : forall prefix w,
  InT w vocab ->
  le (total_loss (prefix ++ [req_pick_best_token prefix]))
     (total_loss (prefix ++ [w])).
Proof.
  intros prefix w Hw.
  unfold req_pick_best_token.
  destruct vocab as [| w0 rest].
  - inversion Hw.
  - destruct (req_argmin_aux_token_min prefix rest w0
                (total_loss (prefix ++ [w0]))) as [Hmin Hle].
    assert (Hsnd : req (snd (req_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [fst (req_argmin_aux_token prefix rest (w0, total_loss (prefix ++ [w0])))])))
      by exact (req_argmin_aux_token_snd_req prefix rest w0
                  (total_loss (prefix ++ [w0])) (req_refl _)).
    inversion Hw as [Hw0 | y0 l0 Hwrest]; subst.
    + (* w = w0：snd ≤ loss w0（第二分量）沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) Hle).
    + (* w ∈ rest：逐项最小性沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) (Hmin w Hwrest)).
Qed.

End ReqArgminTokenWorld.

(* ============================================================ *)
(* reqArgmin 机·ArgminCorrectness 支（基座 L15288-15425 同构；      *)
(*   (c) 3 件 + 消费面机器，(d) 1 件冻结承接不触及）                *)
(* ============================================================ *)
Section ReqArgminWorld.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {DO : reqDecidableOrder R RIS}.

Variable Token : Set.
Variable total_loss : list Token -> R.

(* 基座 candidate L15301 同形 *)
Definition req_candidate : Set := (Token * R)%type.

(* 基座 argmin_aux L15303-15313 同形 *)
Fixpoint req_argmin_aux (prefix : list Token) (l : list Token)
         (best : req_candidate) : req_candidate :=
  match l with
  | nil => best
  | w :: rest =>
      let loss_w := total_loss (prefix ++ [w]) in
      match rord_le_dec loss_w (snd best) with
      | inl _ => req_argmin_aux prefix rest (w, loss_w)
      | inr _ => req_argmin_aux prefix rest best
      end
  end.

(* 基座 argmin_aux_correct L15315（(c) 件 3）：snd ≤ 初值 + 对 l 内逐项
   最小。归纳 + rord_le_dec 分支 + rnot_le_lt/lt_le_iff 反向支。 *)
Lemma req_argmin_aux_correct :
  forall prefix l best_token best_loss,
    let result := req_argmin_aux prefix l (best_token, best_loss) in
    And (le (snd result) best_loss)
        (forall w : Token, InT w l ->
          le (snd result) (total_loss (prefix ++ [w]))).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss.
  - simpl. split.
    + apply le_refl.
    + intros w HIn. inversion HIn.
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + specialize (IH a (total_loss (prefix ++ [a]))).
      destruct IH as [IH_le IH_min].
      split.
      * exact (le_trans _ (total_loss (prefix ++ [a])) _ IH_le Hle).
      * intros w HIn.
        inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- exact IH_le.
        -- exact (IH_min w Hw).
    + specialize (IH best_token best_loss).
      destruct IH as [IH_le IH_min].
      split.
      * exact IH_le.
      * intros w HIn.
        inversion HIn as [Hw_eq | y0 l0 Hw]; subst.
        -- assert (Hlt : lt best_loss (total_loss (prefix ++ [a])))
             by exact (rnot_le_lt (total_loss (prefix ++ [a])) best_loss Hnot).
           exact (le_trans _ best_loss _ IH_le (lt_le_iff _ _ (inl Hlt))).
        -- exact (IH_min w Hw).
Qed.

(* 机器：基座 argmin_aux_snd_correct L15352 的 req 等词改述版（清单 L315
   「随桥C1 立项可转定义级 (b)」兑现；同 token 支机，零 Leibniz 面）。 *)
Lemma req_argmin_aux_snd_req : forall prefix l best_token best_loss,
  req best_loss (total_loss (prefix ++ [best_token])) ->
  req (snd (req_argmin_aux prefix l (best_token, best_loss)))
      (total_loss (prefix ++ [fst (req_argmin_aux prefix l (best_token, best_loss))])).
Proof.
  intros prefix l. induction l as [| a rest IH]; intros best_token best_loss Hinit.
  - exact Hinit.
  - simpl.
    destruct (rord_le_dec (total_loss (prefix ++ [a])) best_loss) as [Hle | Hnot].
    + exact (IH a (total_loss (prefix ++ [a])) (req_refl _)).
    + exact (IH best_token best_loss Hinit).
Qed.

Variable vocab : list Token.
Variable default_token : Token.

(* 基座 pick_best L15363-15369 同形 *)
Definition req_pick_best (prefix : list Token) : Token :=
  match vocab with
  | nil => default_token
  | w0 :: rest =>
      fst (req_argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))
  end.

(* 基座 pick_best_is_minimal L15377（(c) 件 4）：消费 argmin_aux_correct +
   snd 机（Id 系在 snd 等词伴件上做目标换形一处，req 侧改走 req_le_compat
   运输——清单 L316 判词的 req 落地）。 *)
Theorem req_pick_best_is_minimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (prefix ++ [req_pick_best prefix])) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold req_pick_best.
  destruct vocab as [| w0 rest].
  - inversion HIn.
  - destruct (req_argmin_aux_correct prefix rest w0
                (total_loss (prefix ++ [w0]))) as [Hbest Hmin].
    assert (Hsnd : req (snd (req_argmin_aux prefix rest (w0, total_loss (prefix ++ [w0]))))
                      (total_loss (prefix ++ [fst (req_argmin_aux prefix rest (w0, total_loss (prefix ++ [w0])))])))
      by exact (req_argmin_aux_snd_req prefix rest w0
                  (total_loss (prefix ++ [w0])) (req_refl _)).
    inversion HIn as [Hw_eq | y0 l0 Hwrest]; subst.
    + (* w = w0：snd ≤ loss w0（Hbest 第一分量）沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) Hbest).
    + (* w ∈ rest：逐项最小性（Hmin）沿 Hsnd 换形 *)
      exact (req_le_compat _ _ _ _ Hsnd (req_refl _) (Hmin w Hwrest)).
Qed.

(* 基座 dynamics L15372-15374 同形（贪心动力学：追加 pick_best） *)
Definition req_dynamics (s : list Token) : list Token :=
  s ++ [req_pick_best s].

(* 基座 dynamics_greedy_locally_optimal L15407（(c) 件 5，别名件）：
   req_pick_best_is_minimal 经 req_dynamics 展开直配。 *)
Theorem req_dynamics_greedy_locally_optimal :
  forall prefix w,
    InT w vocab ->
    le (total_loss (req_dynamics prefix)) (total_loss (prefix ++ [w])).
Proof.
  intros prefix w HIn.
  unfold req_dynamics.
  exact (req_pick_best_is_minimal prefix w HIn).
Qed.

End ReqArgminWorld.

(* ---- (d) 冻结清单（清单 §7.3 L141/L142/L144/L145/L147 + §7.9 L315 判定；
     nat/list 层 Id 机器与 Leibniz 等词伴件，零证明行） ----
   InT_head_extend（CW219 L2451）/ argmin_aux_token_mem（L2461）/
   pick_best_in_vocab'（L2531）/ pick_best_in_vocab（L2575）/
   argmin_aux_token_snd_correct（L2517）/ argmin_aux_snd_correct（L15352）。
   前四件：list 载体 Id 机器（规划书 §1.1 边界 2；跨接口复用口径同清单 §7.12
   grpo_count_one 消费 count 机先例）。后两件：Id 形不迁；其消费面由本件 req
   等词改述机 req_argmin_aux_token_snd_req / req_argmin_aux_snd_req（清单 L144/
   L315「随桥C1 立项可转定义级 (b)」注记兑现）+ 接口字段 req_le_compat 运输承担。 *)
