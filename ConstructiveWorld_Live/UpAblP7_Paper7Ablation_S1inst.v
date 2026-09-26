(* UpAblP7_Paper7Ablation_S1inst.v —— p7a_expf_wd / p7a_expf_mono_le_do *) (*   的柯西实数实例件（S1inst）。                                       *)
(* 使命：Paper7Ablation §1 五参数位（expf/expf_pos/expf_zero/           *) (*   expf_plus/expf_mono_lt）全显实例件：以柯西实数具体件输入五参数位，  *)
(*   对 p7a_expf_wd 的实例化语句给出装配与直证双覆盖证明，并兑现         *) (*   p7a_expf_mono_le_do 的实例形。                                     *)
(* 用途：消融论实例级验证——wd 无须独立假设、由三字段                    *) (*   {expf_plus, expf_zero, expf_pos} 消去链兑现的判定，                 *)
(*   在本库柯西实数模型上做实例级复核；mono_le 由 mono_lt +              *) (*   序分解 + wd 路径兑现（字段面 6→5 的模型级复核）。                   *)
(* 使用面（上游出口真名）：                                             *) (*   p7a_expf_wd（Id 层消融定理，对照使用）；                           *)
(*   p7a_expf_mono_le_do（DO 三分路线）；                               *) (*   cauchy_real_exp / cauchy_real_exp_pos / cauchy_real_exp_zero       *)
(*   （S03_QExp，参数1-3）；cauchy_real_exp_plus / cauchy_real_exp_mono /  *) (*   cauchy_real_exp_wd（S07_RealSetoidExpLog，参数4/参数5/直证形）；      *)
(*   real_le := Or(real_lt, real_eq)（S02_CauchyComplete）；             *) (*   mult_cancel_l（S01_BaseRing，消去链源引理）；                        *)
(*   bs_lo_pos（AttnDoeblin，旁证：一跳 expf_pos 已证）。                *) (* 双覆盖互证说明：                                                     *)
(*   装配形 s1inst_p7a_expf_wd——按 p7a_expf_wd 的乘逆消去链在           *) (*   柯西实例上重演：三字段具体件输入；链中同余步（Id 层                 *)
(*   id_cong expf）在 real_eq 层须另证，由独立子引理                     *) (*   s1inst_exp_cong_zero（e 在零点连续，自 S03 原语自证）与实层         *)
(*   乘消去 s1inst_real_mult_cancel_l（仿 S01 mult_cancel_l）补足；      *) (*   直证形 s1inst_p7a_expf_wd_direct——直接使用 cauchy_real_exp_wd；     *)
(*   互证 s1inst_dual_cover——抽象消融语句（p7a_expf_wd 全参形，          *) (*   Paper7Ablation 实际使用）与柯西实例语句（装配形与直证形两路           *)
(*   各自证得同一语句）对照合取，两覆盖路线相互独立。                    *)
(* 拓扑注记（如实）：S01 RealInterfaceEnhanced 全库无具体实例            *)
(*   （Id 形字段在柯西 Real 上不可满足），故实例输入走 S07 柯西实数层    *)
(*   唯一实际使用路径；DecidableOrder 在柯西实例不可满足（强三分           *)
(*   LPO 不可证，reqDecidableOrder 全库零实例），故 mono_le 实例形       *)
(*   走 real_le 的 Or 编码分解（lt 支=参数5 严格单调，eq 支=装配形 wd）     *)
(*   ——DO 三分的模型级对应形。                                          *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                    *)
(*   S07_RealSetoidExpLog、Paper7Ablation；Stdlib QArith/List/Bool/      *)
(*   Arith/Setoid/Morphisms/Lia。                                       *)
(* 对标：mathlib Real.exp 的同余性与单调性之实例级对应；stdlib Q 段      *)
(*   仅作算术演算。                                                     *)
(* 构造性注记：语句面全 Set 层（real_eq/real_lt/real_le/Or）；           *)
(*   非平凡真证（零点连续子引理＋实层乘消去＋三字段消去链＋Or 分解）；   *)
(*   零新开口、无经典逻辑。                                             *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。           *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import Paper7Ablation.

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ############ 子件一：e 在零点连续（装配链同余步补足） ########### *)
(* x == 0 ⟹ e^x == 1。自 S03 原语自证，不使用 cauchy_real_exp_wd。 *)
Lemma s1inst_exp_cong_zero : forall x : Real,
  real_eq x real_zero -> real_eq (cauchy_real_exp x) real_one.
Proof.
  intros x Hx. destruct x as [u Hu].
  unfold real_eq in Hx |- *.
  intros eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) u Hu))
    as [M [HMpos HM]].
  assert (HMnonnegT : QleT' 0 M) by (apply qltT_leT'; exact HMpos).
  destruct (exp_series_arch M HMnonnegT) as [C [HC1 HC]].
  assert (HCposT : QltT 0 C).
  { apply (qltT_leT'_ltT 0 1 C). exact qltT_0_1. exact HC1. }
  assert (HCpos : Qlt 0 C) by (apply QltT_to_Qlt; exact HCposT).
  assert (HCnonneg : Qle 0 C) by (apply (Qlt_le_weak 0 C); exact HCpos).
  assert (HepsC : QltT 0 (eps / (2 * C))).
  { apply (qltT_div_pos eps (2 * C)).
    - exact Heps.
    - apply (qmult_ltT_0_compat 2 C). exact qltT_0_2. exact HCposT. }
  destruct (Hx (eps / (2 * C))%Q HepsC) as [N1 HN1].
  exists N1. intros n Hn.
  cbn [projT1] in HN1.
  simpl.
  (* 目标：QltT (Qabs (exp_partial n (u n) - 1)) eps *)
  assert (Hshape : Qabs (exp_partial n (u n) - exp_partial n 0)
                   == Qabs (exp_partial n (u n) - 1)).
  { rewrite (exp_partial_zero n). reflexivity. }
  apply (qltT_eq_compat_l (Qabs (exp_partial n (u n) - exp_partial n 0))
                          (Qabs (exp_partial n (u n) - 1))
                          eps Hshape).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - 0) * C) _).
  - apply (Qle_trans _ (Qabs (u n - 0) * exp_series n M) _).
    + exact (exp_partial_lipschitz (u n) 0 M n HMnonnegT (HM n) HMnonnegT).
    + apply (Qmult_le_compat_nonneg (Qabs (u n - 0)) (Qabs (u n - 0))
                                    (exp_series n M) C).
      * split; [apply Qabs_nonneg | apply Qle_refl].
      * split.
        -- apply (exp_series_nonneg n M HMnonnegT).
        -- apply QleT'_to_Qle. apply (HC n).
  - apply (Qle_lt_trans _ ((eps / (2 * C)) * C) _).
    + apply (Qmult_le_compat_r (Qabs (u n - 0)) (eps / (2 * C)) C).
      * apply (Qlt_le_weak (Qabs (u n - 0)) (eps / (2 * C))).
        apply QltT_to_Qlt. exact (HN1 n Hn).
      * exact HCnonneg.
    + apply (Qle_lt_trans _ (eps / 2) _).
      * apply qeq_le.
        assert (Hc : (eps / (2 * C)) * C == eps / 2).
        { unfold Qdiv. field.
          all: try (apply q_neq_of_lt; apply (Qmult_lt_0_compat 2 C)).
          all: try (unfold Qlt; simpl; lia).
          all: try (exact HCpos).
          all: try (apply q_neq_of_lt; exact HCpos). }
        exact Hc.
      * apply (q_half_lt_self eps). apply QltT_to_Qlt. exact Heps.
Qed.

(* ############ 子件二：实层乘法左消去（仿 S01 mult_cancel_l） ##### *)
Lemma s1inst_real_mult_cancel_l : forall a b c : Real,
  real_lt real_zero a ->
  real_eq (real_mult a b) (real_mult a c) -> real_eq b c.
Proof.
  intros a b c Ha Habc.
  assert (H1 : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b))
                       (real_mult (real_inv_pos a Ha) (real_mult a c))).
  { apply (RealSetoid.real_eq_mult_compat (real_inv_pos a Ha) (real_mult a b)
             (real_inv_pos a Ha) (real_mult a c)).
    - apply real_eq_refl.
    - exact Habc. }
  assert (Hinv : real_eq (real_mult (real_inv_pos a Ha) a) real_one).
  { apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha)) _).
    - apply real_mult_comm.
    - exact (real_inv_pos_correct a Ha). }
  assert (Honeb : real_eq (real_mult real_one b) b).
  { apply (real_eq_trans _ (real_mult b real_one) _).
    - apply real_mult_comm.
    - exact (real_mult_one b). }
  assert (Honec : real_eq (real_mult real_one c) c).
  { apply (real_eq_trans _ (real_mult c real_one) _).
    - apply real_mult_comm.
    - exact (real_mult_one c). }
  assert (Hlb : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b)) b).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) a) b) _).
    - exact (real_mult_assoc (real_inv_pos a Ha) a b).
    - apply (real_eq_trans _ (real_mult real_one b) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) b real_one b).
        * exact Hinv.
        * apply real_eq_refl.
      + exact Honeb. }
  assert (Hrc : real_eq (real_mult (real_inv_pos a Ha) (real_mult a c)) c).
  { apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos a Ha) a) c) _).
    - exact (real_mult_assoc (real_inv_pos a Ha) a c).
    - apply (real_eq_trans _ (real_mult real_one c) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_inv_pos a Ha) a) c real_one c).
        * exact Hinv.
        * apply real_eq_refl.
      + exact Honec. }
  apply (real_eq_trans b (real_mult (real_inv_pos a Ha) (real_mult a b)) c).
  - apply real_eq_sym. exact Hlb.
  - exact (real_eq_trans _ _ _ H1 Hrc).
Qed.

(* ############ 装配形：三字段 {plus, zero, pos} 消去链输入参数位 ######## *)
(* p7a_expf_wd 的实例化语句：柯西实数 e 的 real_eq 同余性，由      *)
(* cauchy_real_exp_plus / cauchy_real_exp_zero / cauchy_real_exp_pos *)
(* 三字段件与子件一/二重演 p7a_expf_wd 的乘逆消去链，不使用直证形。 *)
Theorem s1inst_p7a_expf_wd : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  assert (Ha1 : real_eq (real_mult (cauchy_real_exp a)
                                  (cauchy_real_exp (real_opp b))) real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus a (real_opp b))) _).
    - apply real_eq_sym. exact (cauchy_real_exp_plus a (real_opp b)).
    - apply (s1inst_exp_cong_zero (real_plus a (real_opp b))).
      apply (real_eq_trans (real_plus a (real_opp b))
             (real_plus b (real_opp b)) real_zero).
      + exact (RealSetoid.real_eq_plus_compat a (real_opp b) b (real_opp b)
                 Hab (real_eq_refl (real_opp b))).
      + exact (real_plus_opp b). }
  assert (Hb1 : real_eq (real_mult (cauchy_real_exp b)
                                  (cauchy_real_exp (real_opp b))) real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus b (real_opp b))) _).
    - apply real_eq_sym. exact (cauchy_real_exp_plus b (real_opp b)).
    - apply (s1inst_exp_cong_zero (real_plus b (real_opp b))).
      exact (real_plus_opp b). }
  apply (s1inst_real_mult_cancel_l (cauchy_real_exp (real_opp b))
           (cauchy_real_exp a) (cauchy_real_exp b)
           (cauchy_real_exp_pos (real_opp b))).
  apply (real_eq_trans
           (real_mult (cauchy_real_exp (real_opp b)) (cauchy_real_exp a))
           real_one
           (real_mult (cauchy_real_exp (real_opp b)) (cauchy_real_exp b))).
  - apply (real_eq_trans _ (real_mult (cauchy_real_exp a)
                     (cauchy_real_exp (real_opp b))) _).
    + apply real_mult_comm.
    + exact Ha1.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (cauchy_real_exp b)
                      (cauchy_real_exp (real_opp b))) _).
    + apply real_mult_comm.
    + exact Hb1.
Qed.

(* ############ 直证形：直接使用 cauchy_real_exp_wd（双覆盖之一） ### *)
Theorem s1inst_p7a_expf_wd_direct : forall a b : Real,
  real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  exact cauchy_real_exp_wd.
Qed.

(* ############ 互证：抽象消融语句与柯西实例语句对照合取 ############ *)
(* 类型注记：抽象支为 Type 层 forall（接口量化），And 为 Set×Set      *)
(* 装不下，故以 sigT 封装——首支=抽象消融语句的证明（p7a_expf_wd      *)
(* 全参形，Paper7Ablation 实际使用），尾支=柯西实例语句的装配∧直证双覆盖。*)
Corollary s1inst_dual_cover :
  sigT
    (fun _ : forall {RI : S01_BaseRing.RealInterfaceEnhanced}
                    (expf : @S01_BaseRing.R RI -> @S01_BaseRing.R RI),
       (forall x : @S01_BaseRing.R RI,
          @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (expf x)) ->
       S01_BaseRing.Id (expf (@S01_BaseRing.zero RI))
                       (@S01_BaseRing.one RI) ->
       (forall a b : @S01_BaseRing.R RI,
          S01_BaseRing.Id (expf (@S01_BaseRing.plus RI a b))
                          (@S01_BaseRing.mult RI (expf a) (expf b))) ->
       forall a b : @S01_BaseRing.R RI,
         S01_BaseRing.Id a b -> S01_BaseRing.Id (expf a) (expf b) =>
     And
       (forall a b : Real,
          real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))
       (forall a b : Real,
          real_eq a b -> real_eq (cauchy_real_exp a) (cauchy_real_exp b))).
Proof.
  (* 抽象消融支：裸引 p7a_expf_wd 会触发 ?RI 急切实例化而与带 RI
     首量化的期望型失配，故以 λ 全参显式应用（@ 全参形）。 *)
  exists (fun (RI : S01_BaseRing.RealInterfaceEnhanced)
             (expf : @S01_BaseRing.R RI -> @S01_BaseRing.R RI)
             (expf_pos : forall x : @S01_BaseRing.R RI,
                 @S01_BaseRing.lt RI (@S01_BaseRing.zero RI) (expf x))
             (expf_zero : S01_BaseRing.Id (expf (@S01_BaseRing.zero RI))
                            (@S01_BaseRing.one RI))
             (expf_plus : forall a b : @S01_BaseRing.R RI,
                 S01_BaseRing.Id (expf (@S01_BaseRing.plus RI a b))
                                 (@S01_BaseRing.mult RI (expf a) (expf b))) =>
           @p7a_expf_wd RI expf expf_pos expf_zero expf_plus).
  split.
  - exact s1inst_p7a_expf_wd.
  - exact s1inst_p7a_expf_wd_direct.
Qed.

(* ############ mono_le 实例形：mono_lt + Or 分解 + wd 路径 ######## *)
(* real_le := Or (real_lt) (real_eq)（S02_CauchyComplete）：lt 支走参数5 严格单调 *)
(* cauchy_real_exp_mono，eq 支走装配形 wd——DO 三分在柯西实例不可   *)
(* 满足（强三分 LPO 不可证），Or 编码即其模型级对应形。             *)
Theorem s1inst_p7a_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab.
  unfold real_le in Hab |- *.
  destruct Hab as [Hlt | Heq].
  - (* lt 支：参数5 严格单调直给 *)
    left. exact (cauchy_real_exp_mono a b Hlt).
  - (* eq 支：装配形 wd 路径（三字段消去链） *)
    right. exact (s1inst_p7a_expf_wd a b Heq).
Qed.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions s1inst_exp_cong_zero.
Print Assumptions s1inst_real_mult_cancel_l.
Print Assumptions s1inst_p7a_expf_wd.
Print Assumptions s1inst_p7a_expf_wd_direct.
Print Assumptions s1inst_dual_cover.
Print Assumptions s1inst_p7a_expf_mono_le.
