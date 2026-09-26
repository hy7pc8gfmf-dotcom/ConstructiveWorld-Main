(* ==========================================================================)
   UpAblP6_UniformLimit.v — 一致收敛第一刀的单点供给实例
   使命: pa6ul_strict_first_cut：词表非空、γ 正性与 gap 供给（pa6ul_gap_le_supply/gamma_pos_supply）组装的首个严格截断推论；定义件 vocab/z/gamma/eq_dec/m_in。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、S04_RealExpLogConv、S07_RealSetoidExpLog、CW_ConstructiveWorld_219、AttnHardLimit218、UpReqAttnUniformLimit；Stdlib List、Arith。
   对标: 一致收敛论证中的首项截断（ε-一致逼近的标准手法）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
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
