(* ==========================================================================)
   UpReqMisc5B.v —— req 层杂项束：向量世界转写层、热力学与语言模型命题面、
   GRPO 计数机与希尔伯特空间正交分解构造件
   使命：本件形式化三面。其一，向量世界类转写层（reqStateSpace /
     reqStateSpaceExt / reqHilbertSpace / reqSumOver，Id 接口逐字段 req 副本）。
     其二，热力学与语言模型核心命题：PropositionConvergenceCore
     （req_core_claim5_holds / req_boltzmann_factor_pos / req_boltzmann_prob_pos）、
     ThermodynamicsInstance（req_thermo_core_claim3_holds / _claim5_holds）、
     ConvergenceTheorem（req_entropy_gradient_strict_mono / req_gradient_diff_from_zero /
     req_gradient_step_recurrence）、SumExpPositive（req_sum_exp_positive）、
     LanguageModelInstance（req_core_claim1/3/5_lm_holds、req_normalized_prob_pos、
     req_prediction_boltzmann_sampling_holds）、GRPONoDup 计数机
     （req_grpo_count_one / req_grpo_uniform_mass）与可微代数面
     （req_compose_diff_decomp / req_dpo_loss_diff_decomp / req_dpo_sigmoid 系）。
     其三，希尔伯特空间正交分解存在性与唯一性
     （req_orthogonal_decomposition_exists / _unique）、Gram-Schmidt 步
     （req_gram_schmidt_step / req_gram_schmidt_pair）与多变量可微代数伴生族。
   依赖：S01_BaseRing 至 S15_TailFEPUp 基座链、UpReqAlgebra、UpReqDist；
     Stdlib List；RealInterfaceEnhancedMod 接口内联。
   对标：mathlib 有限和与热力学分布的构造性 Set 层对应物；内积空间正交投影
     存在性的对应物（本库自建于 req 接口层）。
   构造性：Set 层承载，零承认、零公理；核心件全 Qed；纯 term-mode 组装；
     多态核件提取 Obj.magic=0。诚实边界：节内假设申报三位——
     rprojection_idempotent / rmv_adjoint（未使用，同位保留）；
     rop_lipschitz（被 req_op_lipschitz_compose 使用）。
   编译配方：Rocq 9.1 直调 coqc -q -Q . "" -native-compiler no，cpu_guard 包裹限载。
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
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part 1：向量世界类转写层        *)
(* 等号位分派（登记表 7）：req 接口 req 字段仅定义在 R 上（接口     *)
(* L40471 req : R -> R -> Set）——R 值位等号 req（逐件核对），    *)
(* 向量载体位等号保持 Id（Leibniz 多态，L69；载体无        *)
(* setoid 等位可迁，非降级：Id 即归纳族构造性等号）。            *)
(* ============================================================ *)

(* Id StateSpace L1160-1187 逐字段 req 副本（21 字段） *)
Class reqStateSpace (R : Set) (RIS : RealInterfaceEnhancedSetoid R) := {
  rSS : Set;
  rszero : rSS;
  rsplus : rSS -> rSS -> rSS;
  rsmult : R -> rSS -> rSS;
  rsopp : rSS -> rSS;

  rsplus_assoc : forall a b c : rSS,
    Id (rsplus a (rsplus b c)) (rsplus (rsplus a b) c);
  rsplus_comm : forall a b : rSS, Id (rsplus a b) (rsplus b a);
  rsplus_zero : forall a : rSS, Id (rsplus a rszero) a;
  rsplus_opp : forall a : rSS, Id (rsplus a (rsopp a)) rszero;
  rsmult_one : forall a : rSS, Id (rsmult one a) a;
  rsmult_assoc : forall (a b : R) (x : rSS),
    Id (rsmult a (rsmult b x)) (rsmult (mult a b) x);
  rsmult_distrib_r : forall (a : R) (x y : rSS),
    Id (rsmult a (rsplus x y)) (rsplus (rsmult a x) (rsmult a y));
  rsmult_distrib_l : forall (a b : R) (x : rSS),
    Id (rsmult (plus a b) x) (rsplus (rsmult a x) (rsmult b x));

  rsmetric : rSS -> rSS -> R;
  rsmetric_sym : forall a b : rSS, @req R RIS (rsmetric a b) (rsmetric b a);
  (* Id smetric_pos L1177 plain le 逐位保留（setoid 接口对应字段已逐 eps 化，
     plain 形为诚实参数位，RestB Part4 先例） *)
  rsmetric_pos : forall a b : rSS, @le R RIS (@zero R RIS) (rsmetric a b);
  rsmetric_zero : forall a b : rSS,
    @req R RIS (rsmetric a b) (@zero R RIS) -> Id a b;
  (* Id smetric_triangle L1180 plain le 同上逐位保留 *)
  rsmetric_triangle : forall a b c : rSS,
    @le R RIS (rsmetric a c) (@plus R RIS (rsmetric a b) (rsmetric b c));

  rclim : (nat -> rSS) -> rSS -> Set;
  rclim_unique : forall u l1 l2, rclim u l1 -> rclim u l2 -> Id l1 l2;
  rcauchy_complete_S :
    forall (u : nat -> rSS),
      (forall eps : R, @lt R RIS (@zero R RIS) eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n -> @lt R RIS (rsmetric (u m) (u n)) eps)) ->
      sigT (fun l : rSS => rclim u l)
}.


(* Id sminus L15525 同形（δ 透明定义转写） *)
Definition rsminus (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (SS : reqStateSpace R RIS) (a b : @rSS R RIS SS) : @rSS R RIS SS :=
  @rsplus R RIS SS a (@rsopp R RIS SS b).

(* Id StateSpaceExtended L24738-24758 逐字段 req 副本（9 字段；
   Id 的 :> 继承改显式 rsse_base 参数位 + 依存模块显式 unpack，零语义差） *)
Class reqStateSpaceExt (R : Set) (RIS : RealInterfaceEnhancedSetoid R) := {
  rsse_base : reqStateSpace R RIS;
  rsmult_zero : forall x : @rSS R RIS rsse_base,
    Id (@rsmult R RIS rsse_base (@zero R RIS) x) (@rszero R RIS rsse_base);
  rsmult_opp : forall (a : R) (x : @rSS R RIS rsse_base),
    Id (@rsmult R RIS rsse_base (@opp R RIS a) x)
       (@rsopp R RIS rsse_base (@rsmult R RIS rsse_base a x));
  rsmult_splus_distrib : forall (a : R) (x y : @rSS R RIS rsse_base),
    Id (@rsmult R RIS rsse_base a (@rsplus R RIS rsse_base x y))
       (@rsplus R RIS rsse_base (@rsmult R RIS rsse_base a x) (@rsmult R RIS rsse_base a y));
  rsnorm : @rSS R RIS rsse_base -> R;
  rsnorm_pos : forall x : @rSS R RIS rsse_base, @le R RIS (@zero R RIS) (rsnorm x);
  rsnorm_zero : forall x : @rSS R RIS rsse_base,
    @req R RIS (rsnorm x) (@zero R RIS) -> Id x (@rszero R RIS rsse_base);
  rsnorm_smult : forall (a : R) (x : @rSS R RIS rsse_base),
    @req R RIS (rsnorm (@rsmult R RIS rsse_base a x))
        (@mult R RIS (@abs R RIS a) (rsnorm x));
  rsnorm_triangle : forall x y : @rSS R RIS rsse_base,
    @le R RIS (rsnorm (@rsplus R RIS rsse_base x y))
       (@plus R RIS (rsnorm x) (rsnorm y));
  rsmetric_snorm : forall u v : @rSS R RIS rsse_base,
    @req R RIS (@rsmetric R RIS rsse_base u v)
        (rsnorm (@rsminus R RIS rsse_base u v))
}.

(* Id HilbertSpace L1260-1276 逐字段 req 副本（9 字段） *)
Class reqHilbertSpace (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (SS : reqStateSpace R RIS) : Set := {
  rinner : @rSS R RIS SS -> @rSS R RIS SS -> R;
  rinner_sym : forall x y : @rSS R RIS SS,
    @req R RIS (rinner x y) (rinner y x);
  rinner_pos : forall x : @rSS R RIS SS, @le R RIS (@zero R RIS) (rinner x x);
  rinner_definite : forall x : @rSS R RIS SS,
    @req R RIS (rinner x x) (@zero R RIS) -> Id x (@rszero R RIS SS);
  rinner_splus_l : forall x y z : @rSS R RIS SS,
    @req R RIS (rinner (@rsplus R RIS SS x y) z)
        (@plus R RIS (rinner x z) (rinner y z));
  rinner_smult_l : forall (a : R) (x y : @rSS R RIS SS),
    @req R RIS (rinner (@rsmult R RIS SS a x) y) (@mult R RIS a (rinner x y));
  rproj : @rSS R RIS SS -> @rSS R RIS SS -> @rSS R RIS SS;
  rproj_linear : forall u v w : @rSS R RIS SS,
    Id (rproj u (@rsplus R RIS SS v w))
       (@rsplus R RIS SS (rproj u v) (rproj u w));
  rproj_orthogonal : forall u v : @rSS R RIS SS,
    @req R RIS (rinner (@rsplus R RIS SS v (@rsopp R RIS SS (rproj u v))) u) (@zero R RIS)
}.

(* Id SumOver L1408-1452 逐字段 req 副本（8 字段） *)
Class reqSumOver (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (SS : reqStateSpace R RIS) : Set := {
  rsum_over_S : (@rSS R RIS SS -> R) -> R;
  rsum_over_S_linear : forall (a : R) (f : @rSS R RIS SS -> R),
    @req R RIS (rsum_over_S (fun s => @mult R RIS a (f s))) (@mult R RIS a (rsum_over_S f));
  rsum_over_S_add : forall f g : @rSS R RIS SS -> R,
    @req R RIS (rsum_over_S (fun s => @plus R RIS (f s) (g s)))
        (@plus R RIS (rsum_over_S f) (rsum_over_S g));
  rsum_over_S_ext : forall f g : @rSS R RIS SS -> R,
    (forall s, @req R RIS (f s) (g s)) -> @req R RIS (rsum_over_S f) (rsum_over_S g);
  rsum_over_S_le : forall f g : @rSS R RIS SS -> R,
    (forall s, @le R RIS (f s) (g s)) -> @le R RIS (rsum_over_S f) (rsum_over_S g);
  rsum_over_S_nonneg : forall f : @rSS R RIS SS -> R,
    (forall s, @le R RIS (@zero R RIS) (f s)) -> @le R RIS (@zero R RIS) (rsum_over_S f);
  rsum_over_S_zero_nonneg : forall f : @rSS R RIS SS -> R,
    (forall s, @le R RIS (@zero R RIS) (f s)) -> @req R RIS (rsum_over_S f) (@zero R RIS) ->
      forall s, @req R RIS (f s) (@zero R RIS);
  rabs_sum_le : forall f : @rSS R RIS SS -> R,
    @le R RIS (@abs R RIS (rsum_over_S f)) (rsum_over_S (fun s => @abs R RIS (f s)))
}.

(* ============================================================ *)
(* Part 2：PropositionConvergenceCore 4 件（Id L1454-1700 依存面） *)
(* ============================================================ *)
Section ReqPropConvCore.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SS : reqStateSpace R RIS} {SO : reqSumOver R RIS SS}.

Let S : Set := @rSS R RIS SS.
Let sumS := @rsum_over_S R RIS SS SO.

(* Id Proposition L1490 / boltzmann_factor L1568 / boltzmann_prob L1572 定义转写 *)
Variable rZ : R.
Variable rZ_pos : lt zero rZ.
Variable rD : R.
Variable rD_pos : lt zero rD.
Variable rk_B : R.
Variable rk_B_pos : lt zero rk_B.

Definition rboltzmann_factor (L : S -> R) (s : S) : R :=
  exp_neg (mult (inv_pos rD rD_pos) (L s)).

Definition rboltzmann_prob (L : S -> R) (s : S) : R :=
  mult (inv_pos rZ rZ_pos) (rboltzmann_factor L s).

(* Id partition_condition L1576（sum_over_S 位置 = rsum_over_S；语句位置 Id→req） *)
Definition rpartition_condition (L : S -> R) : Set :=
  req rZ (sumS (rboltzmann_factor L)).

(* Id CoreClaim5 L1608（ExistsT 位逐字同形；函数等号位逐点化——
   req 仅定义在 R 上，登记表 8：Id p (boltzmann_prob L) →
   forall s, req (p s) (rboltzmann_prob L s)，见证同形） *)
Definition rCoreClaim5 : Set :=
  forall L : S -> R, rpartition_condition L ->
    ExistsT (fun p : S -> R => forall s : S, req (p s) (rboltzmann_prob L s)).

(* Id core_claim5_holds L1619（exists + 自反；定义级闭合） *)
Theorem req_core_claim5_holds : rCoreClaim5.
Proof.
  unfold rCoreClaim5. intros L _.
  exists (fun s => mult (inv_pos rZ rZ_pos)
                        (exp_neg (mult (inv_pos rD rD_pos) (L s)))).
  intro s. unfold rboltzmann_prob, rboltzmann_factor.
  apply req_refl.
Qed.

(* Id boltzmann_factor_pos L1628（exp_neg_pos 字段直引） *)
Theorem req_boltzmann_factor_pos :
  forall (L : S -> R) (s : S), lt zero (rboltzmann_factor L s).
Proof.
  intros L s. unfold rboltzmann_factor. apply exp_neg_pos.
Qed.

(* Id boltzmann_prob_pos L1637（mult_positive + inv_pos_pos + exp_neg_pos 组装） *)
Theorem req_boltzmann_prob_pos :
  forall (L : S -> R) (s : S), lt zero (rboltzmann_prob L s).
Proof.
  intros L s. unfold rboltzmann_prob, rboltzmann_factor.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* Id prediction_fluctuation_scale L1671（exp_neg_le_decr + le_mult_compat_weak
   + lt_le_iff + req_le_plus_nonneg_r（登记表 3）+ one_pos） *)
Theorem req_prediction_fluctuation_scale : forall N : R,
  le (exp_neg (mult (plus N one) (inv_pos rk_B rk_B_pos)))
     (exp_neg (mult N (inv_pos rk_B rk_B_pos))).
Proof.
  intro N.
  apply exp_neg_le_decr.
  apply (le_mult_compat_weak N (plus N one) (inv_pos rk_B rk_B_pos)).
  - apply (lt_le_iff _ _). left. apply inv_pos_pos.
  - apply (req_le_plus_nonneg_r N one (lt_le_iff _ _ (inl one_pos))).
Qed.

End ReqPropConvCore.

(* ============================================================ *)
(* Part 3：ThermodynamicsInstance 2 件（Id L2906-3040 依存面）    *)
(* ============================================================ *)
Section ReqThermoInstance.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable rMicrostate : Set.
Variable rE_total : R.

(* Id E_B L2918（minus → req_minus，登记表 1） *)
Definition rE_B (E_A : R) : R := req_minus rE_total E_A.

Variable rtemperature_A : R -> R.
Variable rtemperature_B : R -> R.
Variable rtemperature_A_pos : forall E_A, lt zero (rtemperature_A E_A).
Variable rtemperature_B_pos : forall E_A, lt zero (rtemperature_B E_A).

(* Id entropy_gradient L2984 定义转写（minus → req_minus） *)
Definition rentropy_gradient (E_A : R) : R :=
  req_minus (inv_pos (rtemperature_A E_A) (rtemperature_A_pos E_A))
            (inv_pos (rtemperature_B (rE_B E_A)) (rtemperature_B_pos (rE_B E_A))).

(* Id CoreClaim3 L3018（语句位置 minus → req_minus） *)
Definition rCoreClaim3 : Set := forall E_A,
  req (rentropy_gradient E_A)
      (req_minus (inv_pos (rtemperature_A E_A) (rtemperature_A_pos E_A))
                 (inv_pos (rtemperature_B (rE_B E_A)) (rtemperature_B_pos (rE_B E_A)))).

(* Id core_claim3_holds L3025（定义展开自反） *)
Theorem req_thermo_core_claim3_holds : rCoreClaim3.
Proof.
  unfold rCoreClaim3, rentropy_gradient. intro E_A. apply req_refl.
Qed.

Variable rHamiltonian : rMicrostate -> R.
Variable rbeta : R.
Variable rpartition_function_t : R.
Variable rpartition_positive_t : lt zero rpartition_function_t.

(* Id boltzmann_prob L3000 定义转写 *)
Definition rboltzmann_prob_t (x : rMicrostate) : R :=
  mult (inv_pos rpartition_function_t rpartition_positive_t)
       (exp_neg (mult rbeta (rHamiltonian x))).

(* Id CoreClaim5 L3026 *)
Definition rCoreClaim5t : Set := forall x : rMicrostate,
  req (rboltzmann_prob_t x)
      (mult (inv_pos rpartition_function_t rpartition_positive_t)
            (exp_neg (mult rbeta (rHamiltonian x)))).

(* Id core_claim5_holds L3032（定义展开自反） *)
Theorem req_thermo_core_claim5_holds : rCoreClaim5t.
Proof.
  unfold rCoreClaim5t, rboltzmann_prob_t. intro x. apply req_refl.
Qed.

End ReqThermoInstance.

(* ============================================================ *)
(* Part 4：ConvergenceTheorem 余 3 件（Id L13837-14010）          *)
(* 语句级口径核对（MinP 卡）：               *)
(*   req_iterate_step_diff<-13880 req_iterate_step_abs_diff<-13929 *)
(*   req_gradient_abs_mono<-13982 —— 已由 UpReqCauchy.v 落盘已证明  *)


(*   单点步差辅件 req_step_diff_point 节内自足）。                *)
(* ============================================================ *)
Section ReqConvTheorem.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable rentropy_gradient : R -> R.
Variable rdynamics : R -> R.
Variable reta : R.
Variable rdynamics_gradient_step : forall x : R,
  req (rdynamics x) (plus x (mult reta (rentropy_gradient x))).
Variable rstrict_concavity : forall x y : R, lt x y -> lt (rentropy_gradient y) (rentropy_gradient x).
Variable rL : R.
Variable rgradient_lipschitz : forall x y : R,
  le (abs (req_minus (rentropy_gradient x) (rentropy_gradient y)))
     (mult rL (abs (req_minus x y))).

(* 单点步差（req 需生辅件；Id iterate_step_diff L13880 基例模式）：
   x_{n+1} − x_n == η·g(x_n) 于任意点 x 的 req 形 *)
Lemma req_step_diff_point : forall x : R,
  req (req_minus (rdynamics x) x) (mult reta (rentropy_gradient x)).
Proof.
  intro x. unfold req_minus.
  exact (req_trans _ _ _
    (req_plus_compat (rdynamics x)
                     (plus x (mult reta (rentropy_gradient x)))
                     (opp x) (opp x)
                     (rdynamics_gradient_step x) (req_refl (opp x)))
    (req_minus_plus_cancel_r x (mult reta (rentropy_gradient x)))).
Qed.

(* Id entropy_gradient_strict_mono L13912（strict_concavity 位别名，exact 平移） *)
Theorem req_entropy_gradient_strict_mono : forall x y : R,
  lt x y -> lt (rentropy_gradient y) (rentropy_gradient x).
Proof.
  intros x y Hxy. exact (rstrict_concavity x y Hxy).
Qed.

(* Id gradient_diff_from_zero L13920（gradient_lipschitz 于 y := zero 特化） *)
Theorem req_gradient_diff_from_zero : forall x : R,
  le (abs (req_minus (rentropy_gradient x) (rentropy_gradient zero)))
     (mult rL (abs (req_minus x zero))).
Proof.
  intro x. exact (rgradient_lipschitz x zero).
Qed.

(* Id gradient_step_recurrence L13944：|g(x_{n+1}) − g(x_n)| ≤ (L·|η|)·|g(x_n)|。
   iterate 位以定义级归约接 req_step_diff_point（iterate f (S n) x ≡ f (iterate f n x)），
   |·| 换形走 abs_compat + abs_mult 字段（零跨模块 Require）。 *)
Theorem req_gradient_step_recurrence : forall (E_A : R) (n : nat),
  le (abs (req_minus (rentropy_gradient (iterate rdynamics (Datatypes.S n) E_A))
                     (rentropy_gradient (iterate rdynamics n E_A))))
     (mult (mult rL (abs reta)) (abs (rentropy_gradient (iterate rdynamics n E_A)))).
Proof.
  intros E_A n.
  assert (Hdiff : req (req_minus (iterate rdynamics (Datatypes.S n) E_A)
                                 (iterate rdynamics n E_A))
                      (mult reta (rentropy_gradient (iterate rdynamics n E_A))))
    by exact (req_step_diff_point (iterate rdynamics n E_A)).
  assert (Habsd : req (abs (req_minus (iterate rdynamics (Datatypes.S n) E_A)
                                      (iterate rdynamics n E_A)))
                      (mult (abs reta) (abs (rentropy_gradient (iterate rdynamics n E_A)))))
    by exact (req_trans _ _ _
               (req_abs_compat _ _ Hdiff)
               (abs_mult reta (rentropy_gradient (iterate rdynamics n E_A)))).
  apply (le_trans _ (mult rL (mult (abs reta) (abs (rentropy_gradient (iterate rdynamics n E_A))))) _).
  - exact (le_id_r _ _ _
            (req_mult_compat rL rL _ _ (req_refl rL) Habsd)
            (rgradient_lipschitz (iterate rdynamics (Datatypes.S n) E_A)
                                 (iterate rdynamics n E_A))).
  - exact (le_id_r _ _ _
            (mult_assoc rL (abs reta)
               (abs (rentropy_gradient (iterate rdynamics n E_A))))
            (le_refl _)).
Qed.

End ReqConvTheorem.

(* ============================================================ *)
(* Part 5：SumExpPositive 1 件（Id KeyProofs 区 L15240-15284）    *)
(* 孪生已证明注记：本件同时已证明 LanguageModelInstance 孪生          *)
(* sum_exp_positive（Id L1875）——同语句同证（清单 §7.8 结论）。   *)
(* ============================================================ *)
Section ReqSumExpPos.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable rToken : Set.
Variable rneg_log_prob : list rToken -> rToken -> R.

(* Id sum_exp L15257 定义转写（载体重建，定义级） *)
Fixpoint req_sum_exp (prefix : list rToken) (l : list rToken) : R :=
  match l with
  | nil => zero
  | w :: rest => plus (exp_neg (rneg_log_prob prefix w)) (req_sum_exp prefix rest)
  end.

(* Id sum_exp_positive L15266（归纳 + lt_id_r 换形 + plus_positive；前提
   Not (Id l nil) 为 list 层参数位原样保留） *)
Lemma req_sum_exp_positive :
  forall (prefix l : list rToken), Not (Id l nil) -> lt zero (req_sum_exp prefix l).
Proof.
  intros prefix l. induction l as [| w rest IH].
  - intros Hnil. contradiction Hnil. apply id_refl.
  - intros _. simpl.
    destruct rest as [| w' rest'].
    + exact (lt_id_r _ _ _
               (req_sym _ _ (plus_zero (exp_neg (rneg_log_prob prefix w))))
               (exp_neg_pos (rneg_log_prob prefix w))).
    + apply plus_positive.
      * apply exp_neg_pos.
      * apply IH. intro H. inversion H.
Qed.

End ReqSumExpPos.

(* ============================================================ *)
(* Part 6：LanguageModelInstance 6 件（Id L1777-2000 依存面；      *)
(*         sum_exp_positive 孪生 L1875 已由 Part 5 已证明）         *)
(* 签名变化（登记表 2）：Id loss_of_proposition 用无前提 log_inv；   *)
(*   req 形 log_inv 带 lt zero 前提 → 新增 3 正性参数位           *)
(*   rhas_verb_pos/rsemantics_coherent_pos/rstyle_appropriate_pos  *)
(*   （逐位登记）。core_claim3 证明体为纯代数链（不解开       *)
(*   rtotal_loss），参数位仅入语句签名。                           *)
(* ============================================================ *)
Section ReqLangModelInstance.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable rToken : Set.
Variable rvocab : list rToken.
Variable rvocab_nonempty : Not (Id rvocab nil).
Variable rneg_log_prob : list rToken -> rToken -> R.
Variable rhas_verb : list rToken -> R.
Variable rsemantics_coherent : list rToken -> R.
Variable rstyle_appropriate : list rToken -> R.
Variable ralpha_grammar : R.
Variable ralpha_semantics : R.
Variable ralpha_style : R.
Variable rprop_pos : forall (P : list rToken -> R) (s : list rToken), lt zero (P s).
Variable rhas_verb_pos : forall s : list rToken, lt zero (rhas_verb s).
Variable rsemantics_coherent_pos : forall s : list rToken, lt zero (rsemantics_coherent s).
Variable rstyle_appropriate_pos : forall s : list rToken, lt zero (rstyle_appropriate s).

(* Id loss_of_proposition L1807（log 前提化，登记表 2） *)
Definition rloss_of_prop (c : list rToken -> R) (s : list rToken)
    (Hc : lt zero (c s)) : R := log_inv (c s) Hc.

(* Id sequence_loss_prefix L1796 / sequence_loss L1801 定义转写 *)
Fixpoint rsequence_loss_prefix (prefix : list rToken) (s : list rToken) : R :=
  match s with
  | nil => zero
  | w :: rest => plus (rneg_log_prob prefix w) (rsequence_loss_prefix (prefix ++ [w]) rest)
  end.

Definition rsequence_loss (s : list rToken) : R := rsequence_loss_prefix nil s.

(* Id total_loss L1818 定义转写（正性前提显式化） *)
Definition rtotal_loss (s : list rToken) : R :=
  plus (rsequence_loss s)
       (plus (mult ralpha_grammar (rloss_of_prop rhas_verb s (rhas_verb_pos s)))
             (plus (mult ralpha_semantics
                         (rloss_of_prop rsemantics_coherent s (rsemantics_coherent_pos s)))
                   (mult ralpha_style
                         (rloss_of_prop rstyle_appropriate s (rstyle_appropriate_pos s))))).

(* Id force L1822 定义转写（minus → req_minus） *)
Definition rforce (s : list rToken) (w : rToken) : R :=
  opp (req_minus (rtotal_loss (s ++ [w])) (rtotal_loss s)).

(* Id LangProp L1803 / partition_function L1868 / partition_positive L1889 /
   normalized_prob L1975 定义转写（sum_exp 位 = Part 5 req_sum_exp 闭名） *)
Definition rLangProp : Set := list rToken -> R.

Definition rpartition_function (prefix : list rToken) : R :=
  req_sum_exp rToken rneg_log_prob prefix rvocab.

Definition rpartition_positive (prefix : list rToken) :
    lt zero (rpartition_function prefix) :=
  req_sum_exp_positive rToken rneg_log_prob prefix rvocab rvocab_nonempty.

Definition rnormalized_prob (prefix : list rToken) (w : rToken) : R :=
  mult (exp_neg (rneg_log_prob prefix w))
       (inv_pos (rpartition_function prefix) (rpartition_positive prefix)).

(* Id exp_neg_positive L1872（exp_neg_pos 字段 1 行平移） *)
Lemma req_exp_neg_positive : forall x : R, lt zero (exp_neg x).
Proof. intro x. apply exp_neg_pos. Qed.

(* Id core_claim1_holds L1931（prop_pos 假设位同构，exact 位平移） *)
Theorem req_core_claim1_lm_holds :
  forall (P : rLangProp) (s : list rToken), lt zero (P s).
Proof. exact rprop_pos. Qed.

(* Id core_claim3_holds L1938：req_opp_plus + req_double_neg + plus_comm
   三步链（清单结论依存面；minus → req_minus unfold 后直接匹配） *)
Theorem req_core_claim3_lm_holds : forall (s : list rToken) (w : rToken),
  req (rforce s w) (req_minus (rtotal_loss s) (rtotal_loss (s ++ [w]))).
Proof.
  intros s w. unfold rforce, req_minus.
  assert (Hopp : req (opp (plus (rtotal_loss (s ++ [w])) (opp (rtotal_loss s))))
                     (plus (opp (rtotal_loss (s ++ [w]))) (opp (opp (rtotal_loss s))))).
  { exact (req_opp_plus (rtotal_loss (s ++ [w])) (opp (rtotal_loss s))). }
  assert (Hneg : req (plus (opp (rtotal_loss (s ++ [w]))) (opp (opp (rtotal_loss s))))
                     (plus (opp (rtotal_loss (s ++ [w]))) (rtotal_loss s))).
  { exact (req_plus_compat (opp (rtotal_loss (s ++ [w]))) (opp (rtotal_loss (s ++ [w])))
                           (opp (opp (rtotal_loss s))) (rtotal_loss s)
                           (req_refl (opp (rtotal_loss (s ++ [w]))))
                           (req_double_neg (rtotal_loss s))). }
  exact (req_trans _ _ _ Hopp
    (req_trans _ _ _ Hneg
      (plus_comm (opp (rtotal_loss (s ++ [w]))) (rtotal_loss s)))).
Qed.

(* Id core_claim5_holds L1949（定义展开自反） *)
Theorem req_core_claim5_lm_holds : forall (prefix : list rToken) (w : rToken),
  req (rnormalized_prob prefix w)
      (mult (exp_neg (rneg_log_prob prefix w))
            (inv_pos (rpartition_function prefix) (rpartition_positive prefix))).
Proof.
  intros prefix w. unfold rnormalized_prob. apply req_refl.
Qed.

(* Id normalized_prob_pos L1981（mult_positive + exp_neg_pos + inv_pos_pos 组装） *)
Theorem req_normalized_prob_pos : forall (prefix : list rToken) (w : rToken),
  lt zero (rnormalized_prob prefix w).
Proof.
  intros prefix w. unfold rnormalized_prob. apply mult_positive.
  - apply exp_neg_pos.
  - apply inv_pos_pos.
Qed.

(* Id prediction_boltzmann_sampling_holds L1993（与 core_claim5 同内容命名件） *)
Theorem req_prediction_boltzmann_sampling_holds :
  forall (prefix : list rToken) (w : rToken),
  req (rnormalized_prob prefix w)
      (mult (exp_neg (rneg_log_prob prefix w))
            (inv_pos (rpartition_function prefix) (rpartition_positive prefix))).
Proof.
  intros prefix w. apply req_refl.
Qed.

End ReqLangModelInstance.

(* ============================================================ *)
(* Part 7：GRPONoDup R 侧余 4 件（Id Module UpGRPO219 L113533-113860） *)
(* count 机器（count_g/removeT_g/nodup_g/not_InT/InT 系）= nat/list *)
(* Id 层，跨接口原样复用（登记表 4；结论 @Id nat 原样零迁移）；       *)
(* R 值求和位 = UpReqDist reqd_list_sum_g（其 GRPO 节为 FEP 区      *)
(* L23793 块，与本块同名异体，零冲突）。                            *)
(* ============================================================ *)
Section ReqGrpoMisc.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable rGroup : Set.
Variable rgroup_enum : list rGroup.
Variable rgrp_eq_dec : forall i j : rGroup, Or (Id i j) (Not (Id i j)).
Variable rnd_g : UpGRPO219.nodup_g rGroup rgroup_enum.

Let rG : R := reqd_of_nat (length rgroup_enum).
Variable rG_pos : lt zero rG.

(* ---- 正性供给组（签名保持式，形态二外部供给）----
   rG_pos 原样保留为接口参数位：枚举可取空表，此时 rG 化为零元、
   严格正不可证（反模型＝空枚举）。以下三件给出非空条件下的无条件
   推导，供实例化时点直接取用；出节签名零变动。
   树内对照锚：reqd_of_nat_pos（UpReqMpDomain，S k 形）——本件自持
   重演同构证明，维持依赖面零新增（不引 UpReqMpDomain）。 *)
Lemma rgrp_of_nat_S_pos : forall k : nat, lt zero (reqd_of_nat (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - (* 基座：reqd_of_nat 1 定义层即 plus one zero，换形回 one 后由 one_pos 闭合 *)
    apply (lt_id_r zero one (reqd_of_nat (Datatypes.S O))).
    + apply (req_trans one (plus one zero) (reqd_of_nat (Datatypes.S O))).
      * apply (req_sym (plus one zero) one). apply plus_zero.
      * apply req_refl.
    + exact one_pos.
  - (* 步：reqd_of_nat (S (S k)) 定义层即 1 + reqd_of_nat (S k)，双正性相加保持 *)
    apply (lt_id_r zero (plus one (reqd_of_nat (Datatypes.S k)))
                      (reqd_of_nat (Datatypes.S (Datatypes.S k)))).
    + apply req_refl.
    + apply plus_positive. exact one_pos. exact IH.
Qed.

(* 非空列表的嵌入正性：InT 见证给出长度后继形（sigT 见证出口） *)
Theorem rgrp_G_pos_of_nonempty :
  forall l : list rGroup,
    sigT (fun t : rGroup => InT t l) -> lt zero (reqd_of_nat (length l)).
Proof.
  intros l. destruct l as [| x rest].
  - (* 空表：InT 见证不可构造，inversion 消去 *)
    intros [t Ht]. inversion Ht.
  - (* 非空：长度为后继形，正性由 rgrp_of_nat_S_pos 直接给出 *)
    intros _. exact (rgrp_of_nat_S_pos (length rest)).
Qed.

(* 本节枚举位 rG_pos 的实例化时点供给：枚举非空时无条件成立 *)
Theorem rgrp_G_pos_of_nonempty_enum :
  sigT (fun t : rGroup => InT t rgroup_enum) -> lt zero rG.
Proof.
  intro Hne. exact (rgrp_G_pos_of_nonempty rgroup_enum Hne).
Qed.

(* Id UpGRPO219.grpo_count_one L113775：结论 @Id nat 原样，count 机跨接口复用（1 行组装） *)
Theorem req_grpo_count_one : forall (l : list rGroup) (Hnd : UpGRPO219.nodup_g rGroup l)
    (j : rGroup), InT j l -> Id (UpGRPO219.count_g rGroup rgrp_eq_dec j l) (Datatypes.S O).
Proof.
  intros l Hnd j Hin. exact (UpGRPO219.grpo_count_one rGroup rgrp_eq_dec l Hnd j Hin).
Qed.

(* Id list_sum_g_zero_fn L113609（归纳 + plus_zero 换形；前提 InT 位原样） *)
Lemma req_list_sum_g_zero_fn : forall (f : rGroup -> R) (l : list rGroup),
  (forall i : rGroup, InT i l -> req (f i) zero) ->
  req (reqd_list_sum_g rGroup f l) zero.
Proof.
  intros f l. induction l as [| x rest IH]; intro H.
  - apply req_refl.
  - cbn [reqd_list_sum_g].
    assert (IHrest : req (reqd_list_sum_g rGroup f rest) zero).
    { apply IH. intro i. intro Hin. exact (H i (InT_next i x rest Hin)). }
    apply (req_trans _ (plus zero (reqd_list_sum_g rGroup f rest)) _).
    + apply (req_plus_compat (f x) zero (reqd_list_sum_g rGroup f rest)
                             (reqd_list_sum_g rGroup f rest)
                             (H x (InT_here x rest)) (req_refl _)).
    + exact (req_trans _ _ _
               (plus_comm zero (reqd_list_sum_g rGroup f rest))
               (req_trans _ _ _
                 (plus_zero (reqd_list_sum_g rGroup f rest))
                 IHrest)).
Qed.

(* Id split_count_one_id L113720 的 req 需求生：count == 1 ⟹
   Σ l f == f j + Σ (removeT j l) f（Id 级 count 事实以 destruct 代换运送，
   零改写战术） *)
Lemma req_split_count_one : forall (f : rGroup -> R) (j : rGroup) (l : list rGroup),
  Id (UpGRPO219.count_g rGroup rgrp_eq_dec j l) (Datatypes.S O) ->
  req (reqd_list_sum_g rGroup f l)
      (plus (f j) (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j l))).
Proof.
  intros f j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [UpGRPO219.count_g] in Hc. cbn [UpGRPO219.removeT_g reqd_list_sum_g].
    destruct (rgrp_eq_dec x j) as [Hxj | Hnxj].
    + assert (Hc0 : Id (UpGRPO219.count_g rGroup rgrp_eq_dec j rest) O).
        exact (id_cong Nat.pred Hc).
      apply (req_plus_compat (f x) (f j)
               (reqd_list_sum_g rGroup f rest)
               (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))
               (match Hxj in (Id _ y) return (req (f x) (f y)) with
                | id_refl => req_refl _ end)
               (match id_sym (UpGRPO219.count_zero_remove_id rGroup rgrp_eq_dec j rest Hc0)
                in (Id _ y) return
                  (req (reqd_list_sum_g rGroup f rest)
                       (reqd_list_sum_g rGroup f y))
                with id_refl => req_refl _ end)).
    + destruct (rgrp_eq_dec x j) as [Hyt2 | Hnyt2].
      * exact (match Hnxj Hyt2 with end).
      * exact (req_trans _ _ _
          (req_plus_compat (f x) (f x)
             (reqd_list_sum_g rGroup f rest)
             (plus (f j)
                (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest)))
             (req_refl (f x)) (IH Hc))
          (req_trans _ _ _
            (plus_assoc (f x) (f j)
               (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest)))
            (req_trans _ _ _
              (req_plus_compat (plus (f x) (f j)) (plus (f j) (f x))
                 (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))
                 (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))
                 (plus_comm (f x) (f j)) (req_refl _))
              (req_sym _ _ (plus_assoc (f j) (f x)
                 (reqd_list_sum_g rGroup f (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rest))))))).
Qed.

(* Id grpo_indicator_sum_one L113793（grp_eq_dec 判定原样 + req 组装） *)
Theorem req_grpo_indicator_sum_one : forall j : rGroup,
  InT j rgroup_enum ->
  req (reqd_list_sum_g rGroup
         (fun i : rGroup => match rgrp_eq_dec i j with
                            | inl _ => one
                            | inr _ => zero
                            end)
         rgroup_enum)
      one.
Proof.
  intro j. intro Hin.
  assert (Hc1 : Id (UpGRPO219.count_g rGroup rgrp_eq_dec j rgroup_enum) (Datatypes.S O))
    by exact (UpGRPO219.grpo_count_one rGroup rgrp_eq_dec rgroup_enum rnd_g j Hin).
  assert (Hfj : req (match rgrp_eq_dec j j with
                     | inl _ => one
                     | inr _ => zero
                     end) one).
  { destruct (rgrp_eq_dec j j) as [Hjj | Hjj].
    - apply req_refl.
    - exact (match Hjj (id_refl : Id j j) with end). }
  assert (Hrest : req (reqd_list_sum_g rGroup
                         (fun i : rGroup => match rgrp_eq_dec i j with
                                            | inl _ => one
                                            | inr _ => zero
                                            end)
                         (UpGRPO219.removeT_g rGroup rgrp_eq_dec j rgroup_enum)) zero).
  { apply req_list_sum_g_zero_fn.
    intro i. intro HinR.
    destruct (rgrp_eq_dec i j) as [Hxj | Hnxj].
    - exact (match (UpGRPO219.remove_notin_aux rGroup rgrp_eq_dec j i rgroup_enum HinR) Hxj with end).
    - apply req_refl. }
  exact (req_trans _ _ _
    (req_split_count_one _ j rgroup_enum Hc1)
    (req_trans _ _ _
      (req_plus_compat _ _ _ _ Hfj Hrest)
      (plus_zero one))).
Qed.

(* Id grpo_uniform_mass L113832（req_list_sum_g_linear + 组装；
   G 位置 = reqd_of_nat (length rgroup_enum)，G_pos 参数位同构） *)
Theorem req_grpo_uniform_mass : forall j : rGroup,
  InT j rgroup_enum ->
  req (reqd_list_sum_g rGroup
         (fun i : rGroup => mult (inv_pos rG rG_pos)
            (match rgrp_eq_dec i j with
             | inl _ => one
             | inr _ => zero
             end))
         rgroup_enum)
      (inv_pos rG rG_pos).
Proof.
  intro j. intro Hin.
  apply (req_trans _ (mult (inv_pos rG rG_pos)
         (reqd_list_sum_g rGroup
            (fun i : rGroup => match rgrp_eq_dec i j with
                               | inl _ => one
                               | inr _ => zero
                               end)
            rgroup_enum)) _).
  - apply req_list_sum_g_linear.
  - exact (req_trans _ _ _
      (req_mult_compat (inv_pos rG rG_pos) (inv_pos rG rG_pos) _ one
         (req_refl (inv_pos rG rG_pos)) (req_grpo_indicator_sum_one j Hin))
      (mult_one (inv_pos rG rG_pos))).
Qed.

End ReqGrpoMisc.

(* ============================================================ *)
(* Part G：DifferentiableLemmas 代数面 11 件（Id L25673-26304）    *)
(* 零记录依存语句位置 minus →  *)
(* req_minus（登记表 1）；log 依存位置前提化 + 同位参数位（登记表 2）。   *)

(* ============================================================ *)
Section ReqDiffAlgebra.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ---- 自持助手 1：平方四项展开（req 需求生，Id 系 destruct 免费） ---- *)
Lemma req_square_expand4 : forall a h : R,
  req (mult (plus a h) (plus a h))
      (plus (mult a a) (plus (mult a h) (plus (mult h a) (mult h h)))).
Proof.
  intros a h.
  apply (req_trans _ (plus (mult a (plus a h)) (mult h (plus a h))) _).
  - exact (req_mult_plus_distr_r a h (plus a h)).
  - apply (req_trans _ (plus (plus (mult a a) (mult a h))
                             (plus (mult h a) (mult h h))) _).
    + apply (req_plus_compat _ _ _ _ (distrib a a h) (distrib h a h)).
    + exact (req_sym _ _ (plus_assoc (mult a a) (mult a h)
                           (plus (mult h a) (mult h h)))).
Qed.

(* ---- 自持助手 2：头部对消 plus (plus W T) (opp W) == T ---- *)
Lemma req_plus_cancel_head : forall W T : R,
  req (plus (plus W T) (opp W)) T.
Proof.
  intros W T.
  apply (req_trans _ (plus (opp W) (plus W T)) _).
  - exact (plus_comm (plus W T) (opp W)).
  - apply (req_trans _ (plus (plus (opp W) W) T) _).
    + exact (plus_assoc (opp W) W T).
    + apply (req_trans _ (plus zero T) _).
      * apply (req_plus_compat (plus (opp W) W) zero T T
                               (req_trans _ _ _ (plus_comm (opp W) W) (plus_opp W))
                               (req_refl T)).
      * exact (req_trans _ _ _ (plus_comm zero T) (plus_zero T)).
Qed.

(* Id compose_diff_decomp L25673：误差分解核（纯环；req_minus 展开 + req 代数链） *)
Lemma req_compose_diff_decomp : forall (A B C D G g0 h : R),
  req (req_minus A (plus B (mult (mult C D) h)))
      (plus (req_minus A (plus B (mult C (req_minus G g0))))
            (mult C (req_minus (req_minus G g0) (mult D h)))).
Proof.
  intros A B C D G g0 h.
  assert (Hcancel : forall Y : R, req (plus (opp (plus B Y)) Y) (opp B)).
  {
    intro Y.
    apply (req_trans _ (plus (plus (opp B) (opp Y)) Y) _).
    - apply (req_plus_compat (opp (plus B Y)) (plus (opp B) (opp Y)) Y Y
                             (req_opp_plus B Y) (req_refl Y)).
    - apply (req_trans _ (plus (opp B) (plus (opp Y) Y)) _).
      + apply (req_sym _ _ (plus_assoc (opp B) (opp Y) Y)).
      + apply (req_trans _ (plus (opp B) zero) _).
        * apply (req_plus_compat (opp B) (opp B) (plus (opp Y) Y) zero
                                 (req_refl (opp B))).
          exact (req_trans _ _ _ (plus_comm (opp Y) Y) (plus_opp Y)).
        * apply plus_zero.
  }
  assert (Hre : forall Y Y2 : R,
    req (plus (plus A (opp (plus B Y))) (plus Y (opp Y2)))
        (plus A (opp (plus B Y2)))).
  {
    intros Y Y2.
    apply (req_trans _ (plus A (plus (plus (opp (plus B Y)) Y) (opp Y2))) _).
    - exact (req_trans _ _ _
              (req_sym _ _ (plus_assoc A (opp (plus B Y)) (plus Y (opp Y2))))
              (req_plus_compat A A _ _
                (req_refl A) (plus_assoc (opp (plus B Y)) Y (opp Y2)))).
    - apply (req_trans _ (plus A (plus (opp B) (opp Y2))) _).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_plus_compat _ _ _ _ (Hcancel Y) (req_refl (opp Y2))).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_sym _ _ (req_opp_plus B Y2)).
  }
  unfold req_minus.
  apply (req_trans _ (plus A (opp (plus B (mult C (mult D h))))) _).
  - exact (req_plus_compat A A _ _ (req_refl A)
            (req_opp_compat (plus B (mult (mult C D) h)) (plus B (mult C (mult D h)))
              (req_plus_compat B B (mult (mult C D) h) (mult C (mult D h))
                (req_refl B)
                (req_sym (mult C (mult D h)) (mult (mult C D) h) (mult_assoc C D h))))).
  - apply req_sym.
    exact (req_trans _ _ _
      (req_plus_compat (plus A (opp (plus B (mult C (req_minus G g0)))))
                       (plus A (opp (plus B (mult C (req_minus G g0)))))
                       (mult C (plus (req_minus G g0) (opp (mult D h))))
                       (plus (mult C (req_minus G g0)) (opp (mult C (mult D h))))
                       (req_refl _)
                       (req_trans _ _ _
                         (distrib C (req_minus G g0) (opp (mult D h)))
                         (req_plus_compat (mult C (req_minus G g0))
                                          (mult C (req_minus G g0))
                                          (mult C (opp (mult D h)))
                                          (opp (mult C (mult D h)))
                                          (req_refl _)
                                          (req_opp_mult_l C (mult D h)))))
      (Hre (mult C (req_minus G g0)) (mult C (mult D h)))).
Qed.

(* Id half_le_one L25729：inv_2 ≤ 1（two_pos 位 = UpReqAlgebra req_two_pos） *)
Lemma req_half_le_one : le (inv_pos (plus one one) req_two_pos) one.
Proof.
  exact (le_id_l _ _ _
    (req_sym _ _ (mult_one (inv_pos (plus one one) req_two_pos)))
    (le_id_r _ _ _
      (req_trans _ _ _
        (mult_comm (inv_pos (plus one one) req_two_pos) (plus one one))
        (inv_pos_correct (plus one one) req_two_pos))
      (req_le_mult_compat_r (inv_pos (plus one one) req_two_pos) one (plus one one)
        (lt_le_iff _ _ (inl (inv_pos_pos (plus one one) req_two_pos)))
        (req_le_plus_nonneg_r one one (lt_le_iff _ _ (inl one_pos)))))).
Qed.

(* Id half_le_self L25748：eps/2 ≤ eps（非负系数） *)
Lemma req_half_le_self : forall a : R, le zero a ->
  le (mult (inv_pos (plus one one) req_two_pos) a) a.
Proof.
  intros a Ha.
  apply (le_trans _ (mult one a) _).
  - exact (le_mult_compat_weak _ _ _ Ha req_half_le_one).
  - exact (le_id_l _ _ _ (req_trans _ _ _ (mult_comm one a) (mult_one a)) (le_refl a)).
Qed.

(* Id minus_plus_zero_r L26076：(a+b) − c = (a−c) + b *)
Lemma req_minus_plus_zero_r : forall a b c : R,
  req (req_minus (plus a b) c) (plus (req_minus a c) b).
Proof.
  intros a b c. unfold req_minus.
  exact (req_trans _ _ _
    (req_sym _ _ (plus_assoc a b (opp c)))
    (req_trans _ _ _
      (req_plus_compat a a (plus b (opp c)) (plus (opp c) b)
                       (req_refl a) (plus_comm b (opp c)))
      (plus_assoc a (opp c) b))).
Qed.

(* Id square_diff_expand L26092：(x+h−t)² − ((x−t)² + 2(x−t)·h) = h²。
   结构：Hv 换形 → 四项平方展开 → h·u 换位 → 二倍参数位收拢 → plus_assoc
   → 头部对消（req_plus_cancel_head） *)
Lemma req_square_diff_expand : forall x target h : R,
  req (req_minus (mult (req_minus (plus x h) target) (req_minus (plus x h) target))
            (plus (mult (req_minus x target) (req_minus x target))
                  (mult (mult (plus one one) (req_minus x target)) h)))
     (mult h h).
Proof.
  intros x target h.
  assert (Hv : req (req_minus (plus x h) target) (plus (req_minus x target) h))
    by exact (req_minus_plus_zero_r x h target).
  assert (Htwo : req (plus (mult (req_minus x target) h)
                           (mult (req_minus x target) h))
                     (mult (mult (plus one one) (req_minus x target)) h)).
  {
    apply (req_trans _ (plus (mult one (mult (req_minus x target) h))
                             (mult one (mult (req_minus x target) h))) _).
    - apply (req_plus_compat _ _ _ _
              (req_sym (mult one (mult (req_minus x target) h)) (mult (req_minus x target) h)
                (req_mult_one_l (mult (req_minus x target) h)))
              (req_sym (mult one (mult (req_minus x target) h)) (mult (req_minus x target) h)
                (req_mult_one_l (mult (req_minus x target) h)))).
    - apply (req_trans _ (mult (plus one one) (mult (req_minus x target) h)) _).
      + exact (req_sym (mult (plus one one) (mult (req_minus x target) h))
                      (plus (mult one (mult (req_minus x target) h))
                            (mult one (mult (req_minus x target) h)))
                      (req_mult_plus_distr_r one one (mult (req_minus x target) h))).
      + exact (mult_assoc (plus one one) (req_minus x target) h).
  }
  assert (Hs1 : req (plus (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (mult (req_minus (plus x h) target) (req_minus (plus x h) target)) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (req_trans _ _ _
                     (req_mult_compat (req_minus (plus x h) target) (plus (req_minus x target) h) (req_minus (plus x h) target) (plus (req_minus x target) h) Hv Hv)
                     (req_square_expand4 (req_minus x target) h))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  assert (Hx2 : req (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h))))).
  { exact (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_plus_compat (mult (req_minus x target) h) (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)) (plus (mult (req_minus x target) h) (mult h h))
                           (req_refl (mult (req_minus x target) h))
                           (req_plus_compat (mult h (req_minus x target)) (mult (req_minus x target) h) (mult h h) (mult h h)
                           (mult_comm h (req_minus x target))
                           (req_refl (mult h h))))). }
  assert (Hs2 : req (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h))) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_plus_compat (mult (req_minus x target) h) (mult (req_minus x target) h) (plus (mult h (req_minus x target)) (mult h h)) (plus (mult (req_minus x target) h) (mult h h))
                           (req_refl (mult (req_minus x target) h))
                           (req_plus_compat (mult h (req_minus x target)) (mult (req_minus x target) h) (mult h h) (mult h h)
                           (mult_comm h (req_minus x target))
                           (req_refl (mult h h)))))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  assert (Hx3 : req (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h)))).
  { exact (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h))) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_trans _ _ _
                     (plus_assoc (mult (req_minus x target) h) (mult (req_minus x target) h) (mult h h))
                     (req_plus_compat (plus (mult (req_minus x target) h) (mult (req_minus x target) h)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h) (mult h h)
                           Htwo
                           (req_refl (mult h h))))). }
  assert (Hs3 : req (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h)))) (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (req_plus_compat (mult (req_minus x target) (req_minus x target)) (mult (req_minus x target) (req_minus x target)) (plus (mult (req_minus x target) h) (plus (mult (req_minus x target) h) (mult h h))) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))
                           (req_refl (mult (req_minus x target) (req_minus x target)))
                           (req_trans _ _ _
                     (plus_assoc (mult (req_minus x target) h) (mult (req_minus x target) h) (mult h h))
                     (req_plus_compat (plus (mult (req_minus x target) h) (mult (req_minus x target) h)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h) (mult h h)
                           Htwo
                           (req_refl (mult h h)))))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  assert (Hs4 : req (plus (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))) (plus (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))).
  { exact (req_plus_compat (plus (mult (req_minus x target) (req_minus x target)) (plus (mult (mult (plus one one) (req_minus x target)) h) (mult h h))) (plus (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))) (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)))
                           (plus_assoc (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h) (mult h h))
                           (req_refl (opp (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h))))). }
  exact (req_trans _ _ _ Hs1 (req_trans _ _ _ Hs2 (req_trans _ _ _ Hs3 (req_trans _ _ _ Hs4 (req_plus_cancel_head (plus (mult (req_minus x target) (req_minus x target)) (mult (mult (plus one one) (req_minus x target)) h)) (mult h h)))))).
Qed.

Lemma req_dpo_logit_denom_pos : forall x : R, lt zero (plus one (exp_neg x)).
Proof.
  intro x. apply plus_positive.
  - exact one_pos.
  - apply exp_neg_pos.
Qed.

(* sigmoid 定义转写（Id dpo_sigmoid L26255） *)
Definition req_dpo_sigmoid (x : R) : R :=
  inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x).

(* Id dpo_loss_diff_decomp L26247：差分 = log 商（log_div 反向）。
   同位参数位（登记表 2）：setoid 接口无 log_div 字段——抽象层为
   接口义务原样保留（End 时入闭包签名，非公理）；实例化时点供给锚：log_req_compat_real（UpReqU2）与单参桥 log_req_compat（UpReqU2）可直接取用。 *)
Variable req_log_compat_slot :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y), req x y -> req (log x Hx) (log y Hy).

Theorem req_dpo_loss_diff_decomp : forall x h : R,
  req (req_minus (log (plus one (exp_neg (plus x h))) (req_dpo_logit_denom_pos (plus x h)))
                 (log (plus one (exp_neg x)) (req_dpo_logit_denom_pos x)))
     (log (mult (plus one (exp_neg (plus x h)))
                (inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x)))
          (mult_positive (plus one (exp_neg (plus x h)))
                         (inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x))
                         (req_dpo_logit_denom_pos (plus x h))
                         (inv_pos_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x)))).
Proof.
  intros x h. apply req_sym.
  exact (req_log_div req_log_compat_slot
          (plus one (exp_neg (plus x h))) (plus one (exp_neg x))
          (req_dpo_logit_denom_pos (plus x h)) (req_dpo_logit_denom_pos x)).
Qed.

(* Id dpo_sigmoid_pos L26263 *)
Lemma req_dpo_sigmoid_pos : forall x : R, lt zero (req_dpo_sigmoid x).
Proof.
  intro x. unfold req_dpo_sigmoid. apply inv_pos_pos.
Qed.

(* Id dpo_sigmoid_identity L26269：σ(x)·(1+e^{-x}) = 1 *)
Theorem req_dpo_sigmoid_identity : forall x : R,
  req (mult (req_dpo_sigmoid x) (plus one (exp_neg x))) one.
Proof.
  intro x. unfold req_dpo_sigmoid.
  exact (req_trans _ _ _
    (mult_comm (inv_pos (plus one (exp_neg x)) (req_dpo_logit_denom_pos x))
               (plus one (exp_neg x)))
    (inv_pos_correct (plus one (exp_neg x)) (req_dpo_logit_denom_pos x))).
Qed.

(* Id dpo_sigmoid_complement L26280：σ + e^{-x}·σ = 1 *)
Theorem req_dpo_sigmoid_complement : forall x : R,
  req (plus (req_dpo_sigmoid x) (mult (exp_neg x) (req_dpo_sigmoid x))) one.
Proof.
  intro x.
  assert (Hswap : req (plus (mult (req_dpo_sigmoid x) one)
                          (mult (req_dpo_sigmoid x) (exp_neg x)))
                      (plus (req_dpo_sigmoid x) (mult (exp_neg x) (req_dpo_sigmoid x))))
    by exact (req_plus_compat _ _ _ _ (mult_one (req_dpo_sigmoid x))
                            (mult_comm (req_dpo_sigmoid x) (exp_neg x))).
  exact (req_trans _ _ _
    (req_sym _ _ Hswap)
    (req_trans _ _ _
      (req_sym _ _ (distrib (req_dpo_sigmoid x) one (exp_neg x)))
      (req_dpo_sigmoid_identity x))).
Qed.

(* Id dpo_gradient_alt L26298：σ − 1 = −e^{-x}·σ *)
Theorem req_dpo_gradient_alt : forall x : R,
  req (req_minus (req_dpo_sigmoid x) one)
     (opp (mult (exp_neg x) (req_dpo_sigmoid x))).
Proof.
  intro x.
  assert (Hc : req (plus (req_dpo_sigmoid x) (mult (exp_neg x) (req_dpo_sigmoid x))) one)
    by exact (req_dpo_sigmoid_complement x).
  assert (Hcancel : req (plus (req_dpo_sigmoid x) (req_minus one (req_dpo_sigmoid x))) one)
    by exact (req_minus_plus_cancel (req_dpo_sigmoid x) one).
  assert (Hratio : req (mult (exp_neg x) (req_dpo_sigmoid x))
                       (req_minus one (req_dpo_sigmoid x)))
    by exact (req_plus_cancel_l _ _ _ (req_trans _ _ _ Hc (req_sym _ _ Hcancel))).
  assert (Hreduce : req (opp (req_minus one (req_dpo_sigmoid x)))
                        (req_minus (req_dpo_sigmoid x) one)).
  {
    unfold req_minus.
    exact (req_trans _ _ _
      (req_opp_plus one (opp (req_dpo_sigmoid x)))
      (req_trans _ _ _
        (plus_comm (opp one) (opp (opp (req_dpo_sigmoid x))))
        (req_plus_compat (opp (opp (req_dpo_sigmoid x))) (req_dpo_sigmoid x)
                         (opp one) (opp one)
                         (req_double_neg (req_dpo_sigmoid x)) (req_refl (opp one))))).
  }
  exact (req_sym _ _ (req_trans _ _ _ (req_opp_compat _ _ Hratio) Hreduce)).
Qed.

End ReqDiffAlgebra.

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
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part 8：HilbertTheorems 2 件（Id L1281-1400 依存面）           *)
(* ============================================================ *)
Section ReqHilbertTheorems.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SS : reqStateSpace R RIS} {HS : reqHilbertSpace R RIS SS}.

(* 正交残差存在性（Id orthogonal_decomposition_exists L1306）：
   w := v − proj u v 的 sigT 见证；⟨w,u⟩=0（proj_orthogonal 字段 sym 换位）
   + v = proj u v + w（向量 Id 代数链） *)
Theorem req_orthogonal_decomposition_exists :
  forall u v : @rSS R RIS SS,
    sigT (fun w : @rSS R RIS SS =>
      And (@req R RIS (rinner u w) (@zero R RIS))
          (Id v (@rsplus R RIS SS (rproj u v) w))).
Proof.
  intros u v.
  exists (@rsplus R RIS SS v (@rsopp R RIS SS (rproj u v))).
  split.
  - exact (req_trans _ _ _
            (req_sym _ _ (rinner_sym (rsplus v (rsopp (rproj u v))) u))
            (rproj_orthogonal u v)).
  - (* v = proj u v + (v − proj u v)：splus 代数（Id 向量链） *)
    assert (Hopp : Id (@rsplus R RIS SS (rproj u v)
                                  (@rsplus R RIS SS v (@rsopp R RIS SS (rproj u v))))
                      (@rsplus R RIS SS (rproj u v)
                                  (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v)) v)))
      by exact (id_cong (fun x => @rsplus R RIS SS (rproj u v) x)
                        (rsplus_comm v (@rsopp R RIS SS (rproj u v)))).
    assert (Hassoc : Id (@rsplus R RIS SS (rproj u v)
                                    (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v)) v))
                        (@rsplus R RIS SS (@rsplus R RIS SS (rproj u v)
                                                     (@rsopp R RIS SS (rproj u v))) v))
      by exact (rsplus_assoc (rproj u v) (@rsopp R RIS SS (rproj u v)) v).
    assert (Hinv : Id (@rsplus R RIS SS (rproj u v) (@rsopp R RIS SS (rproj u v)))
                      (@rszero R RIS SS))
      by exact (rsplus_opp (rproj u v)).
    assert (Hzero : Id (@rsplus R RIS SS (@rszero R RIS SS) v) v)
      by exact (id_trans (rsplus_comm (@rszero R RIS SS) v) (rsplus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc
              (id_trans (id_cong (fun x => @rsplus R RIS SS x v) Hinv) Hzero)))).
Qed.

(* 正交分解唯一性（Id orthogonal_decomposition_unique L1344）：
   投影的几何确定性——向量 Id 代数（左加 sopp p 折叠） *)
Theorem req_orthogonal_decomposition_unique :
  forall (u v w1 w2 : @rSS R RIS SS),
    @req R RIS (rinner w1 u) (@zero R RIS) ->
    Id v (@rsplus R RIS SS (rproj u v) w1) ->
    @req R RIS (rinner w2 u) (@zero R RIS) ->
    Id v (@rsplus R RIS SS (rproj u v) w2) ->
    Id w1 w2.
Proof.
  intros u v w1 w2 _ Hv1 _ Hv2.
  assert (Heq : Id (@rsplus R RIS SS (rproj u v) w1) (@rsplus R RIS SS (rproj u v) w2))
    by exact (id_trans (id_sym Hv1) Hv2).
  assert (Hc : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w1))
                  (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w2)))
    by exact (id_cong (fun x => @rsplus R RIS SS (@rsopp R RIS SS (rproj u v)) x) Heq).
  assert (Hl1 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w1)) w1).
  {
    assert (H1 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                     (@rsplus R RIS SS (rproj u v) w1))
                    (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w1))
      by exact (rsplus_assoc (@rsopp R RIS SS (rproj u v)) (rproj u v) w1).
    assert (H2 : Id (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w1)
                    (@rsplus R RIS SS (@rszero R RIS SS) w1))
      by exact (id_cong (fun x => @rsplus R RIS SS x w1)
                        (id_trans (rsplus_comm (@rsopp R RIS SS (rproj u v)) (rproj u v))
                                  (rsplus_opp (rproj u v)))).
    assert (H3 : Id (@rsplus R RIS SS (@rszero R RIS SS) w1) w1)
      by exact (id_trans (rsplus_comm (@rszero R RIS SS) w1) (rsplus_zero w1)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  assert (Hl2 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w2)) w2).
  {
    assert (H1 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                     (@rsplus R RIS SS (rproj u v) w2))
                    (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w2))
      by exact (rsplus_assoc (@rsopp R RIS SS (rproj u v)) (rproj u v) w2).
    assert (H2 : Id (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w2)
                    (@rsplus R RIS SS (@rszero R RIS SS) w2))
      by exact (id_cong (fun x => @rsplus R RIS SS x w2)
                        (id_trans (rsplus_comm (@rsopp R RIS SS (rproj u v)) (rproj u v))
                                  (rsplus_opp (rproj u v)))).
    assert (H3 : Id (@rsplus R RIS SS (@rszero R RIS SS) w2) w2)
      by exact (id_trans (rsplus_comm (@rszero R RIS SS) w2) (rsplus_zero w2)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_trans (id_sym Hl1) (id_trans Hc Hl2)).
Qed.

End ReqHilbertTheorems.

(* ============================================================ *)
(* Part 9：GramSchmidt 4 件（Id L24738-24900 依存面；              *)
(*         StateSpaceExtended 面 = reqStateSpaceExt）             *)
(* ============================================================ *)
Section ReqGramSchmidt.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SSE : reqStateSpaceExt R RIS}
        {HS : reqHilbertSpace R RIS (@rsse_base R RIS SSE)}.

Let SSx : reqStateSpace R RIS := @rsse_base R RIS SSE.
Local Existing Instance SSx.

(* Id projection_idempotent L24840 诚实假设位同构（本簇未依存，源模块接口同位保留） *)
Variable rprojection_idempotent : forall u v : @rSS R RIS SSx,
  Id (rproj u (rproj u v)) (rproj u v).

(* Id inner_sopp_l L24791：⟨−x, y⟩ = −⟨x,y⟩（R 值位 req；
   smult_opp 桥的 Id 部分以 match 组合器入 req 链，零改写战术） *)
Lemma req_inner_sopp_l : forall x y : @rSS R RIS SSx,
  @req R RIS (rinner (rsopp x) y) (opp (rinner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (rsmult (opp one) x) (rsopp (rsmult one x)))
    by exact (rsmult_opp one x).
  assert (Hone : Id (rsmult one x) x)
    by exact (rsmult_one x).
  assert (Hsopp : Id (rsmult (opp one) x) (rsopp x))
    by exact (id_trans Hsm (id_cong rsopp Hone)).
  exact (req_trans _ _ _
    (match Hsopp in (Id _ z) return
        (req (rinner z y) (rinner (rsmult (opp one) x) y))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (rinner_smult_l (opp one) x y)
      (req_trans _ _ _
        (req_opp_mult_r one (rinner x y))
        (req_opp_compat (mult one (rinner x y)) (rinner x y)
                        (req_mult_one_l (rinner x y)))))).
Qed.

(* Id inner_szero_l L24812：⟨0, y⟩ = 0（splus_opp + inner_splus_l + inner_sopp_l） *)
Lemma req_inner_szero_l : forall y : @rSS R RIS SSx,
  @req R RIS (rinner rszero y) (zero).
Proof.
  intro y.
  assert (Hz : Id (rsplus y (rsopp y)) rszero)
    by exact (rsplus_opp y).
  exact (req_trans _ _ _
    (match Hz in (Id _ z) return (req (rinner z y) (rinner (rsplus y (rsopp y)) y))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (rinner_splus_l y (rsopp y) y)
      (req_trans _ _ _
        (req_plus_compat (rinner y y) (rinner y y)
                         (rinner (rsopp y) y) (opp (rinner y y))
                         (req_refl (rinner y y)) (req_inner_sopp_l y y))
        (plus_opp (rinner y y))))).
Qed.

(* Id gram_schmidt_step L24844：w := v − proj u v 的正交分量 sigT 见证 *)
Theorem req_gram_schmidt_step : forall u v : @rSS R RIS SSx,
  Not (Id u rszero) ->
  sigT (fun w : @rSS R RIS SSx =>
    And (req (rinner u w) zero)
        (Id v (rsplus (rproj u v) w))).
Proof.
  intros u v Hu.
  exists (rsplus v (rsopp (rproj u v))).
  split.
  - exact (req_trans _ _ _
            (req_sym _ _ (rinner_sym (rsplus v (rsopp (rproj u v))) u))
            (rproj_orthogonal u v)).
  - assert (Hopp : Id (rsplus (rproj u v) (rsplus v (rsopp (rproj u v))))
                      (rsplus (rproj u v) (rsplus (rsopp (rproj u v)) v)))
      by exact (id_cong (fun x => rsplus (rproj u v) x)
                        (rsplus_comm v (rsopp (rproj u v)))).
    assert (Hassoc : Id (rsplus (rproj u v) (rsplus (rsopp (rproj u v)) v))
                        (rsplus (rsplus (rproj u v) (rsopp (rproj u v))) v))
      by exact (rsplus_assoc (rproj u v) (rsopp (rproj u v)) v).
    assert (Hinv : Id (rsplus (rproj u v) (rsopp (rproj u v))) rszero)
      by exact (rsplus_opp (rproj u v)).
    assert (Hzero : Id (rsplus rszero v) v)
      by exact (id_trans (rsplus_comm rszero v) (rsplus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc
              (id_trans (id_cong (fun x => rsplus x v) Hinv) Hzero)))).
Qed.

(* Id gram_schmidt_pair L24874（孪生命名件） *)
Theorem req_gram_schmidt_pair : forall u v : @rSS R RIS SSx,
  Not (Id u rszero) ->
  sigT (fun w : @rSS R RIS SSx =>
    And (req (rinner u w) zero)
        (Id v (rsplus (rproj u v) w))).
Proof.
  intros u v Hu.
  exact (req_gram_schmidt_step u v Hu).
Qed.

End ReqGramSchmidt.

(* ============================================================ *)
(* Part 10：MultivariableDifferentiable 代数面 14 件              *)
(* （Id L26686-27500；DifferentiableMV/MVVec 记录簇） *)
(* ============================================================ *)
Section ReqMultivar.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SSE : reqStateSpaceExt R RIS}
        {HS : reqHilbertSpace R RIS (@rsse_base R RIS SSE)}.

Let SSx : reqStateSpace R RIS := @rsse_base R RIS SSE.
Local Existing Instance SSx.

(* Id inner_splus_r L26722：⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩（sym 换位 ×2） *)
Lemma req_inner_splus_r : forall x y z : @rSS R RIS SSx,
  req (rinner x (rsplus y z)) (plus (rinner x y) (rinner x z)).
Proof.
  intros x y z.
  assert (H1 : req (rinner x (rsplus y z)) (rinner (rsplus y z) x))
    by exact (rinner_sym x (rsplus y z)).
  assert (H2 : req (rinner (rsplus y z) x) (plus (rinner y x) (rinner z x)))
    by exact (rinner_splus_l y z x).
  assert (H3 : req (plus (rinner y x) (rinner z x)) (plus (rinner x y) (rinner x z)))
    by exact (req_plus_compat _ _ _ _ (rinner_sym y x) (rinner_sym z x)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 H3)).
Qed.

(* Id mv_compose_diff_decomp L26739（复用本件 req_compose_diff_decomp；
   D := X、h := one 特化 + mult_one 换形） *)
Lemma req_mv_compose_diff_decomp : forall (A B C G g0 X : R),
  req (req_minus A (plus B (mult C X)))
     (plus (req_minus A (plus B (mult C (req_minus G g0))))
           (mult C (req_minus (req_minus G g0) X))).
Proof.
  intros A B C G g0 X.
  assert (H1 : req (req_minus A (plus B (mult (mult C X) one)))
                   (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (req_minus (req_minus G g0) (mult X one)))))
    by exact (req_compose_diff_decomp A B C X G g0 one).
  (* 左参数位：(mult C X)·one → C·X（mult_assoc 反向 + mult_one） *)
  assert (Hm0 : req (mult (mult C X) one) (mult C X))
    by exact (req_trans _ _ _
              (req_sym _ _ (mult_assoc C X one))
              (req_mult_compat C C (mult X one) X (req_refl C) (mult_one X))).
  assert (Hm1 : req (plus B (mult (mult C X) one)) (plus B (mult C X)))
    by exact (req_plus_compat B B (mult (mult C X) one) (mult C X) (req_refl B) Hm0).
  assert (Hl : req (req_minus A (plus B (mult (mult C X) one)))
                   (req_minus A (plus B (mult C X)))).
  { unfold req_minus.
    exact (req_plus_compat A A (opp (plus B (mult (mult C X) one))) (opp (plus B (mult C X)))
                           (req_refl A)
                           (req_opp_compat (plus B (mult (mult C X) one))
                                           (plus B (mult C X)) Hm1)). }
  (* 右参数位：mult X one → X 于 req_minus 内（unfold + opp 换形） *)
  assert (Hsub : req (plus (req_minus G g0) (opp (mult X one)))
                     (plus (req_minus G g0) (opp X)))
    by exact (req_plus_compat (req_minus G g0) (req_minus G g0)
                              (opp (mult X one)) (opp X)
                              (req_refl (req_minus G g0))
                              (req_opp_compat (mult X one) X (mult_one X))).
  unfold req_minus.
  assert (Hr : req (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (plus (req_minus G g0) (opp (mult X one)))))
                    (plus (req_minus A (plus B (mult C (req_minus G g0))))
                          (mult C (plus (req_minus G g0) (opp X))))).
  { exact (req_plus_compat (req_minus A (plus B (mult C (req_minus G g0))))
                           (req_minus A (plus B (mult C (req_minus G g0))))
                           (mult C (plus (req_minus G g0) (opp (mult X one))))
                           (mult C (plus (req_minus G g0) (opp X)))
                           (req_refl (req_minus A (plus B (mult C (req_minus G g0)))))
                           (req_mult_compat C C (plus (req_minus G g0) (opp (mult X one)))
                                            (plus (req_minus G g0) (opp X))
                                            (req_refl C) Hsub)). }
  exact (req_trans _ _ _ (req_sym _ _ Hl) (req_trans _ _ _ H1 Hr)).
Qed.

(* Id inner_smult_r L27228：⟨x, a·y⟩ = a·⟨x,y⟩（inner_smult_l + sym 换位） *)
Lemma req_inner_smult_r : forall (a : R) (x y : @rSS R RIS SSx),
  req (rinner x (rsmult a y)) (mult a (rinner x y)).
Proof.
  intros a x y.
  assert (H1 : req (rinner x (rsmult a y)) (rinner (rsmult a y) x))
    by exact (rinner_sym x (rsmult a y)).
  assert (H2 : req (rinner (rsmult a y) x) (mult a (rinner y x)))
    by exact (rinner_smult_l a y x).
  assert (H3 : req (mult a (rinner y x)) (mult a (rinner x y)))
    by exact (req_mult_compat a a (rinner y x) (rinner x y)
                             (req_refl a) (rinner_sym y x)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 H3)).
Qed.

(* Id inner_sopp_r L27242：⟨x, −y⟩ = −⟨x,y⟩（smult_opp + inner_smult_r） *)
Lemma req_inner_sopp_r : forall x y : @rSS R RIS SSx,
  req (rinner x (rsopp y)) (opp (rinner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (rsmult (opp one) y) (rsopp (rsmult one y)))
    by exact (rsmult_opp one y).
  assert (Hone : Id (rsmult one y) y)
    by exact (rsmult_one y).
  assert (Hsopp : Id (rsmult (opp one) y) (rsopp y))
    by exact (id_trans Hsm (id_cong rsopp Hone)).
  exact (req_trans _ _ _
    (match id_sym Hsopp in (Id _ z) return
        (req (rinner x (rsopp y)) (rinner x z))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (req_inner_smult_r (opp one) x y)
      (req_trans _ _ _
        (req_opp_mult_r one (rinner x y))
        (req_opp_compat (mult one (rinner x y)) (rinner x y)
                        (req_mult_one_l (rinner x y)))))).
Qed.

(* Id inner_sminus_r L27261：⟨x, u−v⟩ = ⟨x,u⟩ − ⟨x,v⟩ *)
Lemma req_inner_sminus_r : forall x u v : @rSS R RIS SSx,
  req (rinner x (@rsminus R RIS SSx u v)) (req_minus (rinner x u) (rinner x v)).
Proof.
  intros x u v.
  unfold req_minus.
  exact (req_trans _ _ _    (req_inner_splus_r x u (rsopp v))    (req_plus_compat (rinner x u) (rinner x u)                     (rinner x (rsopp v)) (opp (rinner x v))                     (req_refl (rinner x u)) (req_inner_sopp_r x v))).
Qed.

(* Id splus_sminus_cancel L27272：a + (b − a) = b（向量 Id 链） *)
Lemma req_splus_sminus_cancel : forall a b : @rSS R RIS SSx,
  Id (rsplus a (@rsminus R RIS SSx b a)) b.
Proof.
  intros a b.
  unfold rsminus.
  assert (H1 : Id (rsplus a (rsplus b (rsopp a))) (rsplus a (rsplus (rsopp a) b)))
    by exact (id_cong (fun z => rsplus a z) (rsplus_comm b (rsopp a))).
  assert (H2 : Id (rsplus a (rsplus (rsopp a) b)) (rsplus (rsplus a (rsopp a)) b))
    by exact (rsplus_assoc a (rsopp a) b).
  assert (H3 : Id (rsplus (rsplus a (rsopp a)) b) (rsplus rszero b))
    by exact (id_cong (fun z => rsplus z b) (rsplus_opp a)).
  assert (H4 : Id (rsplus rszero b) b)
    by exact (id_trans (rsplus_comm rszero b) (rsplus_zero b)).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

(* Id sopp_szero L27290：−0 = 0（向量 Id 链） *)
Lemma req_sopp_szero : Id (rsopp rszero) rszero.
Proof.
  assert (H1 : Id (rsopp rszero) (rsplus (rsopp rszero) rszero))
    by exact (id_sym (rsplus_zero (rsopp rszero))).
  assert (H2 : Id (rsplus (rsopp rszero) rszero) (rsplus rszero (rsopp rszero)))
    by exact (rsplus_comm (rsopp rszero) rszero).
  assert (H3 : Id (rsplus rszero (rsopp rszero)) rszero)
    by exact (rsplus_opp rszero).
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* Id sminus_sminus_szero L27308：(u−v) − 0 = u−v（向量 Id 链） *)
Lemma req_sminus_sminus_szero : forall u v : @rSS R RIS SSx,
  Id (@rsminus R RIS SSx (@rsminus R RIS SSx u v) rszero) (@rsminus R RIS SSx u v).
Proof.
  intros u v.
  unfold rsminus.
  exact (id_trans (id_cong (fun z => rsplus (rsplus u (rsopp v)) z) req_sopp_szero)                  (rsplus_zero (rsplus u (rsopp v)))).
Qed.

(* Id smetric_sminus_zero L27324：度量平移不变（smetric_snorm +
   sminus_sminus_szero 的 Id 事实以 match 组合器入 req 链） *)
Theorem req_smetric_sminus_zero : forall u v : @rSS R RIS SSx,
  req (rsmetric (@rsminus R RIS SSx u v) rszero) (rsmetric u v).
Proof.
  intros u v.
  exact (req_trans _ _ _    (rsmetric_snorm (@rsminus R RIS SSx u v) rszero)    (req_trans _ _ _      (match req_sminus_sminus_szero u v in (Id _ z) return          (req (rsnorm (@rsminus R RIS SSx (@rsminus R RIS SSx u v) rszero)) (rsnorm z))       with id_refl => req_refl _ end)      (req_sym _ _ (rsmetric_snorm u v)))).
Qed.

(* Id inner_sminus_l L27355：⟨a−b, c⟩ = ⟨a,c⟩ − ⟨b,c⟩ *)
Lemma req_inner_sminus_l : forall a b c : @rSS R RIS SSx,
  req (rinner (@rsminus R RIS SSx a b) c) (req_minus (rinner a c) (rinner b c)).
Proof.
  intros a b c.
  unfold req_minus.
  exact (req_trans _ _ _    (rinner_splus_l a (rsopp b) c)    (req_plus_compat (rinner a c) (rinner a c)                     (rinner (rsopp b) c) (opp (rinner b c))                     (req_refl (rinner a c)) (req_inner_sopp_l b c))).
Qed.

(* Id sminus_zero_cancel L27369：a − b = 0 ⟹ a = b（向量 Id 链） *)
Lemma req_sminus_zero_cancel : forall a b : @rSS R RIS SSx,
  Id (@rsminus R RIS SSx a b) rszero -> Id a b.
Proof.
  intros a b H.
  assert (H1 : Id a (rsplus b (@rsminus R RIS SSx a b)))
    by exact (id_sym (req_splus_sminus_cancel b a)).
  exact (id_trans H1 (id_trans (id_cong (fun z => rsplus b z) H) (rsplus_zero b))).
Qed.

(* 伴随接口（Id mv_adjoint L27376 诚实假设位同构，同位保留） *)
Variable rmv_adjoint : forall (L : @rSS R RIS SSx -> @rSS R RIS SSx),
  sigT (fun Lad : @rSS R RIS SSx -> @rSS R RIS SSx => forall h w : @rSS R RIS SSx,
    req (rinner (L h) w) (rinner h (Lad w))).

(* 算子范数界（Id op_lipschitz L27384 诚实假设位同构，同位保留；
   And = Set 层乘积） *)
Variable rop_lipschitz : forall (L : @rSS R RIS SSx -> @rSS R RIS SSx),
  sigT (fun N : R => And (le zero N) (forall h : @rSS R RIS SSx,
    le (rsmetric (L h) rszero) (mult N (rsmetric h rszero)))).

(* Id mv_adjoint_unique L27383：伴随唯一（⟨h,h'⟩ = 0 ⟹ inner_definite） *)
Lemma req_mv_adjoint_unique : forall (L : @rSS R RIS SSx -> @rSS R RIS SSx)
    (Lad1 Lad2 : @rSS R RIS SSx -> @rSS R RIS SSx),
  (forall h w : @rSS R RIS SSx, req (rinner (L h) w) (rinner h (Lad1 w))) ->
  (forall h w : @rSS R RIS SSx, req (rinner (L h) w) (rinner h (Lad2 w))) ->
  forall w : @rSS R RIS SSx, Id (Lad1 w) (Lad2 w).
Proof.
  intros L Lad1 Lad2 H1 H2 w.
  pose (h := @rsminus R RIS SSx (Lad1 w) (Lad2 w)).
  assert (Hinner : req (rinner h h) zero).
  {
    unfold h.
    apply (req_trans _ _ _ (req_inner_sminus_r h (Lad1 w) (Lad2 w))).
    assert (Hmid : req (rinner h (Lad1 w)) (rinner h (Lad2 w)))
      by exact (req_trans _ _ _ (req_sym _ _ (H1 h w)) (H2 h w)).
    unfold req_minus.
    exact (req_trans _ _ _
      (req_plus_compat (rinner h (Lad1 w)) (rinner h (Lad1 w))
                       (opp (rinner h (Lad2 w))) (opp (rinner h (Lad1 w)))
                       (req_refl (rinner h (Lad1 w)))
                       (req_opp_compat (rinner h (Lad2 w)) (rinner h (Lad1 w))
                                       (req_sym _ _ Hmid)))
      (plus_opp (rinner h (Lad1 w)))).
  }
  assert (Hhzero : Id h rszero) by exact (rinner_definite h Hinner).
  unfold h in Hhzero.
  exact (req_sminus_zero_cancel (Lad1 w) (Lad2 w) Hhzero).
Qed.

(* Id op_lipschitz_compose L27409：|L∘M h| ≤ (N_L·N_M)·|h|
   （le_mult_compat_weak/mult_zero 接口字段链；加位判读经读证收敛：
   Id 证明零 plain 乘积非负依存，零新增假设位） *)
Lemma req_op_lipschitz_compose : forall (L M : @rSS R RIS SSx -> @rSS R RIS SSx),
  sigT (fun N : R => And (le zero N) (forall h : @rSS R RIS SSx,
    le (rsmetric (L (M h)) rszero) (mult N (rsmetric h rszero)))).
Proof.
  intros L M.
  destruct (rop_lipschitz L) as [NL [HNL0 HNL]].
  destruct (rop_lipschitz M) as [NM [HNM0 HNM]].
  exists (mult NL NM).
  split.
  - (* 0 ≤ NL·NM：mult_zero 换形 + le_mult_compat_weak *)
    apply (le_id_l _ (mult zero NM) _).
    + exact (req_trans _ _ _ (req_sym _ _ (mult_zero NM)) (mult_comm NM zero)).
    + exact (le_mult_compat_weak zero NL NM HNM0 HNL0).
  - intros h.
    apply (le_trans _ (mult NL (rsmetric (M h) rszero)) _).
    + exact (HNL (M h)).
    + apply (le_trans _ (mult NL (mult NM (rsmetric h rszero))) _).
      * apply (le_id_l _ (mult (rsmetric (M h) rszero) NL) _).
        { exact (mult_comm NL (rsmetric (M h) rszero)). }
        { apply (le_id_r _ (mult (mult NM (rsmetric h rszero)) NL) _).
          - exact (mult_comm (mult NM (rsmetric h rszero)) NL).
          - exact (le_mult_compat_weak (rsmetric (M h) rszero)
                     (mult NM (rsmetric h rszero)) NL HNL0 (HNM h)). }
      * apply (le_id_l _ (mult (mult NL NM) (rsmetric h rszero)) _).
        { exact (mult_assoc NL NM (rsmetric h rszero)). }
        { exact (le_refl (mult (mult NL NM) (rsmetric h rszero))). }
Qed.

(* Id mv_vec_diff_decomp L27450：通用误差分解（Hcancel + Hre 两段，
   与 req_compose_diff_decomp 同构——Hre Y X 的 req_sym） *)
Lemma req_mv_vec_diff_decomp : forall (A B X Y : R),
  req (req_minus A (plus B X)) (plus (req_minus A (plus B Y)) (req_minus Y X)).
Proof.
  intros A B X Y.
  assert (Hcancel : forall Z : R, req (plus (opp (plus B Z)) Z) (opp B)).
  {
    intro Z.
    apply (req_trans _ (plus (plus (opp B) (opp Z)) Z) _).
    - apply (req_plus_compat (opp (plus B Z)) (plus (opp B) (opp Z)) Z Z
                             (req_opp_plus B Z) (req_refl Z)).
    - apply (req_trans _ (plus (opp B) (plus (opp Z) Z)) _).
      + apply (req_sym _ _ (plus_assoc (opp B) (opp Z) Z)).
      + apply (req_trans _ (plus (opp B) zero) _).
        * apply (req_plus_compat (opp B) (opp B) (plus (opp Z) Z) zero
                                 (req_refl (opp B))).
          exact (req_trans _ _ _ (plus_comm (opp Z) Z) (plus_opp Z)).
        * apply plus_zero.
  }
  assert (Hre : forall Z1 Z2 : R,
    req (plus (plus A (opp (plus B Z1))) (plus Z1 (opp Z2)))
        (plus A (opp (plus B Z2)))).
  {
    intros Z1 Z2.
    apply (req_trans _ (plus A (plus (plus (opp (plus B Z1)) Z1) (opp Z2))) _).
    - exact (req_trans _ _ _
              (req_sym _ _ (plus_assoc A (opp (plus B Z1)) (plus Z1 (opp Z2))))
              (req_plus_compat A A _ _
                (req_refl A) (plus_assoc (opp (plus B Z1)) Z1 (opp Z2)))).
    - apply (req_trans _ (plus A (plus (opp B) (opp Z2))) _).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_plus_compat _ _ _ _ (Hcancel Z1) (req_refl (opp Z2))).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_sym _ _ (req_opp_plus B Z2)).
  }
  unfold req_minus.
  exact (req_sym _ _ (Hre Y X)).
Qed.

End ReqMultivar.
