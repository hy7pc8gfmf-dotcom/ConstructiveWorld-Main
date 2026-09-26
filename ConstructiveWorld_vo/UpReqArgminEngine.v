(* ============================================================ *)
(* UpReqArgminEngine.v *)
(* *)
(* 目的： argmin 选取引擎：有限枚举上的最小值选取与最优性。 *)
(* 主件： rae_pick_mem / rae_pick_optimal：选取的成员性与最优性；mpd_argmin_engine_transport 域搬运。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqDist、UpReqAlignRestB、UpReqAlgebra、UpReqMpDomain。 *)
(* 备注： 序可判定（le/lt 的 Or 形判定）为显式 Variable 前提；有限枚举载体。 *)
(* ============================================================ *)

(* UpReqArgminEngine.v — 席T36：通用 req-list argmin 引擎（20260911）
   ----------------------------------------------------------------
   立论（席A4 深度分析实证，Top-5 候选 A1-3）：mp 域
   mpd_argmin_aux_token_min_mp（UpReqMpDomain.v L394-428）的证明全部
   序积木均为 RIES 接口字段（lt_le_iff / le_id_l / le_trans / le_refl
   皆字段），对任意 (R,RIS) 与任意元素类型通用。Min-P 专用部分仅：
     ① key 函数 total_loss (prefix ++ [w])
     ② vocab/default 挑选包装
     ③ 节变量（vocab_nonempty / temperature 等，argmin 机器不消费）
   本件把 argmin 机器提升为任意 Set 载体 A + 任意 key : A -> R 的
   通用引擎，并在尾段以 mp 域实例回收验证（转换级 transport +
   via_engine 三件）兑现「mp 域 argmin 可由泛化引擎实例化」。

   对位登记表（req 引擎件 <- mp 域原件 @ UpReqMpDomain.v 行号）：
     rae_InT_head_extend            <- mpd_InT_head_extend（L381；A 泛化）
     rae_argmin_aux                 <- mpd_argmin_aux_token（L358；
                                       total_loss (prefix++[w]) → key a）
     rae_argmin_aux_min             <- mpd_argmin_aux_token_min_mp（L394；
                                       逐 tactic 同形，best 打包 (A*R)）
     rae_argmin_aux_snd_correct     <- mpd_argmin_aux_token_snd_correct_mp
                                       （L431）
     rae_argmin_aux_mem             <- mpd_argmin_aux_token_mem（L441）
     rae_pick / rae_pick_mem        <- mpd_pick_best_token（L368）/
                                       mpd_pick_best_in_vocab（L449）
     rae_pick_optimal               <- mpd_pick_best_optimal_mp（L469；
                                       等词伴件运输以 eq_rect 纯 term）
   [回收验证段 MpRecycleProbe]
     mpd_argmin_engine_transport    （消解形定义级转换：mp 机器 = 引擎
                                       在 A:=Token, key:=fun w =>
                                       total_loss (prefix++[w]) 的实例）
     mpd_argmin_aux_token_min_via_engine / _snd_correct_via_engine /
     mpd_argmin_aux_token_mem_via_engine / mpd_pick_best_optimal_via_engine
                                       （mp 域三件由引擎 exact 直供，
                                       核心转换级闭合）
   ----------------------------------------------------------------
   纪律：纯构造性；Set 层语句（Or/And 为 S01 Set 值 A+B / A×B；
   InT 为 stdlib Set 值遍历；等词伴件仅限 snd_correct 恒等式，mp 件
   同位先例）；InT 空支一律 inversion 完成（OrderArgmin 卡：term 级
   空 match 提取面不净）；纯 term/结构化 apply，零目标换形战术；
   核心件 Qed。 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqDist.
Require Import UpReqAlignRestB.
Require Import UpReqAlgebra.
Require Import UpReqMpDomain.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 引擎段 ReqArgminEngine：任意 (R,RIS) × 任意 Set 载体 A        *)
(* ============================================================ *)
Section ReqArgminEngine.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable A : Set.
Variable key : A -> R.

(* 桥假设位 1：le 二分判定（RestB/MpDomain 位 1 同位） *)
Hypothesis rae_le_dec : forall a b : R, Or (le a b) (Not (le a b)).
(* 桥假设位 2：三分判定（仅 min 件 not_le 步消费） *)
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

(* ============================================================ *)
(* 回收验证段 MpRecycleProbe：mp 域 argmin = 引擎实例            *)
(*（位形 = UpReqMpDomain Section ReqMpKernelWorld2 中 argmin 机器  *)
(*  实际消费的假设位：Token / total_loss / 判定位 1+2；其余节变量    *)
(*  vocab_nonempty/temperature/default_token/min_p 不入机器闭包） *)
(* ============================================================ *)
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
   A:=Token, key:=mp_key prefix 假设位下逐支同形——回收结论的转换级
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
