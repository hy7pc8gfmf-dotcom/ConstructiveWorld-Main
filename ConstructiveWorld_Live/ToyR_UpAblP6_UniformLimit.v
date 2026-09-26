(* ============================================================ *)
(* ToyR 玩具证替换件 —— T263 台账席 战役包X（tier2 十四批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   pa6ul_strict_first_cut（原 L135，2 句玩具证）                        *)
(*   pa6ul_gamma_pos_supply（原 L125，1 句玩具证）                        *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T337 恒等守恒更正注记】2026-09-22 包AW十三 台账席（恒等头注更正第三批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测为 *)
(* 恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337 台账。 *)
(* 附记：T277 判级全文恒等；M-Z 域未及件（V 收尾＋X 整包＋Y 起步）第四批直推（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblP6_UniformLimit.v —— alm_uniform_limit 严格档前提的具体实例供给 *)
(* （纯构造性；语句面全 Set 层）。                                     *)
(*                                                                    *)
(* 使命：上游 UpReqAttnUniformLimit 严格档主定理 alm_uniform_limit 的    *)
(*   两枚前提（gamma_pos/gap_le）在并列世界（UpAblAlmConsumption）只能   *)
(*   以 γ=0 形实现，严格档 γ>0 在彼处被反例见证否定，链件只能以剩余      *)
(*   前提形承载——本件以非并列具体世界完成严格档实例供给，三件全 Qed：    *)
(*     ① pa6ul_gap_le_supply：带真间隙具体 z 的 gap_le 严格档供给        *)
(*        （上游前提形逐字；z 两点分段定义形：                           *)
(*         z true=real_one、z false=real_zero，非恒值平凡件；            *)
(*         γ:=real_one；z false+γ=0+1=1=z true 取等紧界——               *)
(*         gap_le 的 ≤ 面取等是最紧供给，间隙真值非 z:=任意平凡值）；     *)
(*     ② pa6ul_gamma_pos_supply：γ>0 直接供给（上游前提形逐字；          *)
(*         real_lt_zero_one 直接给出）；                                *)
(*     ③ pa6ul_strict_first_cut：①②合成的前提包 Corollary——            *)
(*         alm_uniform_limit 全实参直接实例化，严格档主定理在本世界闭合。 *)
(*         对照 UpAblAlmConsumption 头注「剩余前提位                     *)
(*         (n·decay+n·decay)≤k·eps」的 γ=0 档显式保留位：本件为         *)
(*         该保留位的严格档首个实例（以具体世界实例为限，非本体          *)
(*         全域闭合声明）。                                             *)
(*                                                                    *)
(* 载体：bool 双点实例（与 UpAblAlmConsumption 同形）；词表              *)
(*   [true; false]；m:=true；z 分段两点；γ:=real_one。                  *)
(*   非平凡性三点：非 m 副本 false 在表（pa6ul_m_in 真构造）；            *)
(*   false≠true 构造性证书（构造子失配空匹配消解，pa6ul_eq_dec 异支）；   *)
(*   gap_le 在真异点 x=false 实例化（非空泛支），且 γ>0 严格。           *)
(*                                                                    *)
(* 证明路线注记：gap_le 实例不用 minus 展开路（该路经语句级核验在        *)
(*   gap_le 前提形上无适用面），取 real_plus_comm→real_plus_zero 右形→   *)
(*   real_eq_trans→real_eq_le 的换形链，比 minus 展开路少一段；          *)
(*   分段函数构造与库内 bool 两点分段先例同族。                          *)
(* 纪律：全 Qed；前缀 pa6ul_（全库零撞名）；上游零改；                   *)
(*   Print Assumptions 三件核验。                                       *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、S04_RealExpLogConv、 *)
(*   S07_RealSetoidExpLog、CW_ConstructiveWorld_219、AttnHardLimit218、   *)
(*   UpReqAttnUniformLimit。编译配方：coqc 9.1 直调 + cpu_guard。         *)
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

(* ############ 非并列双值最小世界（bool 双点载体） ############ *)

(* 词表：[true; false] 双点表（与 UpAblAlmConsumption 同形）。 *)
Definition pa6ul_vocab : list bool := true :: false :: nil.

(* logit 两点分段定义形：副本支 real_one、非副本支 real_zero—— *)
(* 真间隙载体（非恒值平凡件；库内 bool 两点分段先例同族）。 *)
Definition pa6ul_z (x : bool) : Real :=
  match x with
  | true => real_one
  | false => real_zero
  end.

(* 严格档间隙常量：γ := real_one。 *)
Definition pa6ul_gamma : Real := real_one.

(* 表可判定等词（构造子失配空匹配消解，与 UpAblAlmConsumption 的        *)
(*   almc_eq_dec 同构；Defined 数据面）。 *)
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

(* 表非空证书：[true; false] 异于空表（构造子失配空匹配消解）。 *)
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

(* 上游前提形逐字（UpReqAttnUniformLimit）：
   gap_le : forall x : Token, Not (Id x m) ->
     real_le (real_plus (z x) gamma) (z m) ——
   此处 Token:=bool、z:=pa6ul_z、m:=true、γ:=pa6ul_gamma 直接给出。 *)
Lemma pa6ul_gap_le_supply : forall x : bool, Not (Id x true) ->
  real_le (real_plus (pa6ul_z x) pa6ul_gamma) (pa6ul_z true).
Proof.
  intros x Hx. destruct x as [ | ].
  - (* 情形 x=true：与前提 Not (Id true true) 相斥，空匹配消解。 *)
    exact (match Hx (@id_refl bool true) with end).
  - (* 情形 x=false：0+1 = 1 取等紧界。
       换形链：real_plus_comm（0+1=1+0）→ real_plus_zero 右形（1+0=1）
       → real_eq_trans → real_eq_le 由等式得序。 *)
    exact (RealSetoid.real_eq_le
             (real_plus (pa6ul_z false) pa6ul_gamma) (pa6ul_z true)
             (real_eq_trans (real_plus (pa6ul_z false) pa6ul_gamma)
                (real_plus real_one real_zero) real_one
                (real_plus_comm (pa6ul_z false) real_one)
                (real_plus_zero real_one))).
Qed.

(* ############ ②γ>0 直接供给 ############ *)

(* 上游前提形逐字：gamma_pos : real_lt real_zero gamma。 *)
Lemma pa6ul_gamma_pos_supply : real_lt real_zero pa6ul_gamma.
Proof.
  exact real_lt_zero_one.
Qed.

(* ############ ③前提包 Corollary：严格档主定理实例闭合 ############ *)

(* 上游主定理 alm_uniform_limit 逐字：
   gamma_pos/gap_le 两枚前提在本世界由 ①②直接给出闭合——对照
   UpAblAlmConsumption 头注剩余前提位（γ=0 档显式保留位）的严格档实例。 *)
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
  exact (alm_uniform_limit bool pa6ul_vocab pa6ul_vocab_ne pa6ul_eq_dec           pa6ul_z true pa6ul_m_in pa6ul_gamma pa6ul_gamma_pos_supply           pa6ul_gap_le_supply eps Heps).
Qed.

(* ############ 收尾核验（Print Assumptions 三件 Closed） ############ *)

Print Assumptions pa6ul_gap_le_supply.
Print Assumptions pa6ul_gamma_pos_supply.
Print Assumptions pa6ul_strict_first_cut.
