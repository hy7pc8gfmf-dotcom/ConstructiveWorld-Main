(* ============================================================ *)
(* UpAblP6_UniformLimit.v —— PA6-18 席：UniformLimit 家族严格档首刀   *)
(* （ConstructiveWorld 消融战役论文6，20260920；纯构造性；            *)
(*  全中文头注；语句面全 Set 层）                                    *)
(*                                                              *)
(* 使命（T223 判定的 B3 悬置放电位首刀）：上游 UpReqAttnUniformLimit  *)
(*   严格档主槽 alm_uniform_limit 的两枚前提件（gamma_pos/gap_le）   *)
(*   在并列世界（UpAblAlmConsumption）只能以 γ=0 档真实现，严格档      *)
(*   γ>0 被并列证书驳回，链件只能以余前件形承载——本席以非并列        *)
(*   具体世界完成首刀供给，三件全 Qed：                             *)
(*     ① pa6ul_gap_le_supply：带真间隙具体 z 的 gap_le 严格档供给     *)
(*        （上游槽形 Live 树 :286-287 逐字；z 两点分段定义形：        *)
(*         z true=real_one、z false=real_zero，非恒值平凡件；        *)
(*         γ:=real_one；z false+γ=0+1=1=z true 取等紧界——            *)
(*         gap_le 的 ≤ 面取等是最紧供给，间隙真值非 z:=任意平凡值）；  *)
(*     ② pa6ul_gamma_pos_supply：γ>0 直配供给（上游槽形 :285 逐字；   *)
(*         real_lt_zero_one 直配）；                                *)
(*     ③ pa6ul_strict_first_cut：①②合成前件包 Corollary——           *)
(*         alm_uniform_limit 全实参直配，严格档主槽在本世界闭合。      *)
(*         对照 UpAblAlmConsumption 头注「余前件位                    *)
(*         (n·decay+n·decay)≤k·eps」的 γ=0 档显式保留位：本件为        *)
(*         该保留位的严格档首刀放电（以具体世界实例为限，非本体        *)
(*         全域闭合声明）。                                         *)
(*                                                              *)
(* 载体：bool 直配（照 UpAblAlmConsumption 范式①）；词表             *)
(*   [true; false]；m:=true；z 分段两点；γ:=real_one。               *)
(*   非平凡性三证：非 m 副本 false 在表（pa6ul_m_in 真构造）；        *)
(*   false≠true 构造性证书（J-式指标失配驳回，pa6ul_eq_dec 异支）；    *)
(*   gap_le 在真异点 x=false 实例化（非空泛支），且 γ>0 严格。        *)
(*                                                              *)
(* 检索对账（令十一检索记录详见 T226 台账）：E346 minus→req_minus     *)
(*   反省桥经语句级对账不适用（gap_le 槽形无 minus 面，本席直配       *)
(*   comm→右形加零→eq-trans 桥→eq-le，比 minus 展开路少一段）；       *)
(*   E021/E025 分段函数先例与 bool 两点分段 z 同族参照。              *)
(*                                                              *)
(* 纪律：全 Qed；前缀 pa6ul_（全库实扫零撞名）；上游零改；             *)
(*   未入 order.txt/_CoqProject；Print Assumptions 三件留痕。         *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S07_RealSetoidExpLog.
Require Import CW_ConstructiveWorld_219.
Require Import AttnHardLimit218.
Require Import UpReqAttnUniformLimit.
From Stdlib Require Import List Arith.

(* ############ 非并列双值最小世界（二元词表 flag 载体） ############ *)

(* 词表：二元词表（与 UpAblAlmConsumption 范式①同形直配）。 *)
Definition pa6ul_vocab : list bool := true :: false :: nil.

(* logit 两点分段定义形：副本支 real_one、非副本支 real_zero—— *)
(* 真间隙载体（非恒值平凡件；E021/E025 分段先例同族）。 *)
Definition pa6ul_z (x : bool) : Real :=
  match x with
  | true => real_one
  | false => real_zero
  end.

(* 严格档间隙常量：γ := real_one。 *)
Definition pa6ul_gamma : Real := real_one.

(* 表可判定等词（J-式指标失配范式，照 AlmConsumption almc_eq_dec； *)
(*   Defined 数据面）。 *)
Definition pa6ul_eq_dec (a b : bool) : Or (Id a b) (Not (Id a b)).
Proof.
  destruct a as [ | ]; destruct b as [ | ].
  - exact (@inl _ _ (@id_refl bool true)).
  - exact (@inr (Id true false) (Not (Id true false))
             (fun H : Id true false =>
                match H in Id _ y
                  return (match y with false => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inr (Id false true) (Not (Id false true))
             (fun H : Id false true =>
                match H in Id _ y
                  return (match y with true => Empty_set | _ => unit end) with
                | id_refl => tt
                end)).
  - exact (@inl _ _ (@id_refl bool false)).
Defined.

(* 表非空证书：[true; false] 异于空表（J-式范式）。 *)
Definition pa6ul_vocab_ne : Not (Id pa6ul_vocab nil) :=
  fun H : Id pa6ul_vocab nil =>
    match H in Id _ y
      return (match y with nil => Empty_set | _ => unit end) with
    | id_refl => tt
    end.

(* 副本代表 m := true 入表。 *)
Definition pa6ul_m_in : InT true pa6ul_vocab :=
  @InT_here bool true (false :: nil).

(* ############ ①严格档 gap_le 供给：带真间隙具体 z ############ *)

(* 上游槽形逐字（Live 树 UpReqAttnUniformLimit :286-287）：
   gap_le : forall x : Token, Not (Id x m) ->
     real_le (real_plus (z x) gamma) (z m) ——
   本席 Token:=bool、z:=pa6ul_z、m:=true、γ:=pa6ul_gamma 直配。 *)
Lemma pa6ul_gap_le_supply : forall x : bool, Not (Id x true) ->
  real_le (real_plus (pa6ul_z x) pa6ul_gamma) (pa6ul_z true).
Proof.
  intros x Hx. destruct x as [ | ].
  - (* x = true：与 Not (Id true true) 相斥（AlmConsumption 支一习语） *)
    exact (match Hx (@id_refl bool true) with end).
  - (* x = false：0+1 = 1 取等紧界。
       桥序：real_plus_comm（0+1=1+0）→ real_plus_zero 右形（1+0=1）
       → real_eq_trans → real_eq_le 可解码面。 *)
    exact (RealSetoid.real_eq_le
             (real_plus (pa6ul_z false) pa6ul_gamma) (pa6ul_z true)
             (real_eq_trans (real_plus (pa6ul_z false) pa6ul_gamma)
                (real_plus real_one real_zero) real_one
                (real_plus_comm (pa6ul_z false) real_one)
                (real_plus_zero real_one))).
Qed.

(* ############ ②γ>0 直配供给 ############ *)

(* 上游槽形逐字（Live 树 :285）：gamma_pos : real_lt real_zero gamma。 *)
Lemma pa6ul_gamma_pos_supply : real_lt real_zero pa6ul_gamma.
Proof.
  exact real_lt_zero_one.
Qed.

(* ############ ③前件包 Corollary：严格档主槽首刀放电 ############ *)

(* 上游主槽逐字（Pa6UniLimT226=Live 树 :1428-1457 alm_uniform_limit）：
   gamma_pos/gap_le 两枚前提在本世界由 ①②直配闭合——对照
   UpAblAlmConsumption 头注余前件位（γ=0 档显式保留位）的严格档首刀。 *)
Corollary pa6ul_strict_first_cut :
  forall eps : Real,
    real_lt real_zero eps ->
    sigT (fun T0 =>
      And (real_lt real_zero T0)
        (forall (T : Real) (Ht : real_lt real_zero T),
          real_lt T T0 ->
          real_le
            (real_list_sum bool
               (fun x : bool =>
                  real_abs (real_minus_r
                    (alm_uniform bool pa6ul_vocab pa6ul_eq_dec true
                       pa6ul_m_in x)
                    (w_T bool pa6ul_vocab pa6ul_vocab_ne pa6ul_z T Ht x)))
               pa6ul_vocab)
            eps)).
Proof.
  intros eps Heps.
  exact (alm_uniform_limit bool pa6ul_vocab pa6ul_vocab_ne pa6ul_eq_dec
           pa6ul_z true pa6ul_m_in pa6ul_gamma pa6ul_gamma_pos_supply
           pa6ul_gap_le_supply eps Heps).
Qed.

(* ############ PA 留痕 ############ *)

Print Assumptions pa6ul_gap_le_supply.
Print Assumptions pa6ul_gamma_pos_supply.
Print Assumptions pa6ul_strict_first_cut.
