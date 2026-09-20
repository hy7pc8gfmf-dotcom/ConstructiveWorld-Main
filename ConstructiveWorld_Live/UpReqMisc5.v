(* ============================================================
   T245 包F 台账席 切片二 · 包A 尾巴清偿件一（UpReqMisc5 同名替换，全中文零承认）
   本件为基线原件的同名替换件：语句面、声明序、其余定理与既有版记头注
   逐字保留；仅两条玩具级证明体在替换点重演：
   一、req_core_claim5_holds：exists 见证位定义层展开重演——见证由不透明
       件名 rboltzmann_prob L 改为定义体逐层显式 λ（inv_pos rZ rZ_pos 与
       exp_neg（inv_pos rD rD_pos 与 L s）两层全展开），目标位双定义
       unfold 后自反收口（E379 卡 L455 显式参坑前置，见证同形不变）。
   二、req_core_claim3_lm_holds：换轨中间项显式命名——负号分配腿与
       双重负号腿两条中间 req 以命名断言锚定（Hopp／Hneg），三段收口
       req_trans 复合重演（引擎模板同款形：双锚断言＋收口，见消融50
       UpReqAlgebra req_mult_cancel_r 已验绿体）。
   依赖面零新增：Require 面与原件逐字一致。
   ============================================================ *)
(* ============================================================ *)
(* UpReqMisc5.v *)
(* *)
(* 目的： 热力学核心命题的 req 层杂件第五束。 *)
(* 主件： req_boltzmann_factor_pos / req_boltzmann_prob_pos 与 req_entropy_gradient_strict_mono。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqDist。 *)
(* 备注： 配分正性为接口前提；温度与分布参数以 Section 变量给出。 *)
(* ============================================================ *)

(* UpReqMisc5.v — 签名迁移批 5 波 3 席：杂项完成（其余小节 + 向量世界类转写层）
   工作单：attn\批5基建层处置清单-20260909.md（波3：LMI/PCC/Thermo/ConvThm/SumExp/GRPO
   24 件 + Multivar/Hilbert/GramSchmidt (b|桥) 20 件入 UpReqMisc5B.v + DiffLemmas 代数面
   11 件（纯字段链/环，零记录消费）；differentiable_affine 1 件随 C2 记录桥（波4）结果。
   母本：CW_ConstructiveWorld_219（行号逐件见覆盖核对）；上游：UpReqAlgebra（批1 引擎）
   ----------------------------------------------------------------
   类转写层（清单 §7.11/§9.2 波3「reqStateSpace/HilbertSpace 类转写随本波结果」；
   类体内接口投影一律 @ 全显（载体 rSS ≠ R，实例位手工喂定，零解析歧义）：
     reqStateSpace     ← Id StateSpace L1160-1187（21 字段，语句位 Id→req 逐位镜像；
                          rsmetric_pos/rsmetric_triangle 的 plain le 形为 Id 字段逐位
                          保留——setoid 接口对应字段已逐 eps 化，plain 形作类内假设位，
                          判据 0.2-5/RestB Part4 先例，T2①）
     reqStateSpaceExt  ← Id StateSpaceExtended L24738-24758（9 字段；Id 的 :> 继承
                          改显式 rsse_base 槽 + 消费席显式 unpack，零语义差）
     reqHilbertSpace   ← Id HilbertSpace L1260-1276（9 字段，语句位 Id→req）
     reqSumOver        ← Id SumOver L1408-1452（8 字段，语句位 Id→req）
   ----------------------------------------------------------------
   诚实签名变化登记表（规划书 §7.4，逐件登记）：
   1. minus 非接口字段：语句位 minus → req_minus（UpReqAlgebra δ 透明同形），证明内 unfold；
   2. log 前提化：setoid log/log_inv 带 lt zero 前提——rloss_of_prop（LMI）、
      req_dpo_loss_diff_decomp 各补正性前提/同位假设位（req_log_compat_slot，
      T2①；UpReqAlgebra ReqLogBridge 同槽先例）；
   3. Id le_plus_nonneg_r / mult_plus_distr_r / plus_cancel_l（Id 接口字段）在 req 接口
      缺位 → 消费 UpReqAlgebra 已结果件 req_le_plus_nonneg_r/req_mult_plus_distr_r/
      req_plus_cancel_l（语句同形）；
   4. count 机器（nat/list Id 层）：跨接口原样复用 Module UpGRPO219 已闭名
      （grpo_count_one/count_zero_remove_id/remove_notin_aux/nodup_g/count_g/removeT_g），
   5. iterate（L1394）：多态纯 nat 递归零 Id 内容，跨接口原样复用
      （G09_MiscSmall.v 先例同款）；
   6. two_pos（Id 顶层件）req 侧以 UpReqAlgebra req_two_pos 内联；
   7. 向量载体位等号保持 Id（req 字段仅定义于 R 上，载体无 setoid 等位——
      Part 0 头注）；R 值位等号 req 逐件核对；
   8. 函数等号位逐点化：rCoreClaim5 的 Id p (boltzmann_prob L) →
      forall s, req (p s) (rboltzmann_prob L s)（见证同形，定义级闭合不变）。
   ----------------------------------------------------------------
   覆盖核对（req 件名 -> Id 原件 @ 行号）：
   PCC：req_core_claim5_holds<-1619 req_boltzmann_factor_pos<-1628
        req_boltzmann_prob_pos<-1637 req_prediction_fluctuation_scale<-1671
        （reqSumOver 类<-1408 rboltzmann_factor<-1568 rboltzmann_prob<-1572
          rpartition_condition<-1576 rCoreClaim5<-1608 定义转写）
   Thermo：req_thermo_core_claim3_holds<-3025 req_thermo_core_claim5_holds<-3032
        （rE_B<-2918 rentropy_gradient<-2984 rboltzmann_prob_t<-3000 定义转写）
   ConvThm：req_iterate_step_diff<-13880 req_entropy_gradient_strict_mono<-13912
        req_gradient_diff_from_zero<-13920 req_iterate_step_abs_diff<-13929
        req_gradient_step_recurrence<-13944 req_gradient_abs_mono<-13982
   SumExp：req_sum_exp_positive<-15266（KeyProofs 区；LMI L1875 孪生同模板）
   LMI：req_exp_neg_positive<-1872 req_sum_exp_positive_lm<-1875
        req_core_claim1_lm_holds<-1931 req_core_claim3_lm_holds<-1938
        req_core_claim5_lm_holds<-1949 req_normalized_prob_pos<-1981
        req_prediction_boltzmann_sampling_holds<-1993
        （rsequence_loss_prefix<-1796 rtotal_loss<-1818 rforce<-1822
          rpartition_function<-1870 rnormalized_prob<-1975 定义转写）
   GRPO：req_list_sum_g_zero_fn<-113609 req_grpo_count_one<-113775
        req_grpo_indicator_sum_one<-113793 req_grpo_uniform_mass<-113832
        （req_split_count_one 为 Id split_count_one_id<-113720 的 req 需求生）
   DiffAlgebra：req_compose_diff_decomp<-25673 req_half_le_one<-25729
        req_half_le_self<-25748 req_minus_plus_zero_r<-26076
        req_square_diff_expand<-26092 req_dpo_logit_denom_pos<-26239
        req_dpo_loss_diff_decomp<-26247 req_dpo_sigmoid<-26255(定义)
        req_dpo_sigmoid_pos<-26263 req_dpo_sigmoid_identity<-26269
        req_dpo_sigmoid_complement<-26280 req_dpo_gradient_alt<-26298
   (d) 冻结注记（双层并行，零证明行）：argmin_aux_snd_correct L15352（Leibniz 等号
   伴件）、id_app_nil_r L15436 / id_app_cons_assoc L15443 / sequence_loss_prefix_app
   L15451（list 载体 Id 换形）——归批5 (d) 冻结清单，本件不建。
   ---------------------------------------------------------------- *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part 0：向量世界类转写层（清单 §8 行 4，一次性 ~70 行）        *)
(* 等号位分派（登记表 7）：req 接口 req 字段仅定义在 R 上（接口     *)
(* L40471 req : R -> R -> Set）——R 值位等号 req（逐件核对），    *)
(* 向量载体位等号保持 Id（Leibniz 多态，L69；载体无        *)
(* setoid 等位可迁，非降级：Id 即归纳族构造性等号）。            *)
(* ============================================================ *)

(* Id StateSpace L1160-1187 逐字段 req 镜像（21 字段） *)
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
     plain 形为诚实假设位：判据 0.2-5，RestB Part4 先例） *)
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

(* Id StateSpaceExtended L24738-24758 逐字段 req 镜像（9 字段；
   Id 的 :> 继承改显式 rsse_base 槽 + 消费席显式 unpack，零语义差） *)
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

(* Id HilbertSpace L1260-1276 逐字段 req 镜像（9 字段） *)
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

(* Id SumOver L1408-1452 逐字段 req 镜像（8 字段） *)
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
(* Part A：PropositionConvergenceCore 4 件（Id L1454-1700 消费面） *)
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

(* Id partition_condition L1576（sum_over_S 位 = rsum_over_S；语句位 Id→req） *)
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
(* Part B：ThermodynamicsInstance 2 件（Id L2906-3040 消费面）    *)
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

(* Id CoreClaim3 L3018（语句位 minus → req_minus） *)
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
(* Part C：ConvergenceTheorem 余 3 件（Id L13837-14010）          *)
(* 跨席核对（MinP 卡语句级口径，20260909 04:38）：               *)
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
   |·| 换形走 abs_compat + abs_mult 字段（零跨席 Require）。 *)
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
(* Part D：SumExpPositive 1 件（Id KeyProofs 区 L15240-15284）    *)
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

(* Id sum_exp_positive L15266（归纳 + lt_id_r 换形 + plus_positive；premise
   Not (Id l nil) 为 list 层假设位原样保留，T2①） *)
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
(* Part E：LanguageModelInstance 6 件（Id L1777-2000 消费面；      *)
(*         sum_exp_positive 孪生 L1875 已由 Part D 已证明）         *)
(* 签名变化（登记表 2）：Id loss_of_proposition 用无前提 log_inv；   *)
(*   req 形 log_inv 带 lt zero 前提 → 新增 3 正性假设位           *)
(*   rhas_verb_pos/rsemantics_coherent_pos/rstyle_appropriate_pos  *)
(*   （T2①，逐位登记）。core_claim3 证明体为纯代数链（不解开       *)
(*   rtotal_loss），假设位仅入语句签名。                           *)
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

(* Id total_loss L1818 定义转写（正性前提位显式化） *)
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
   normalized_prob L1975 定义转写（sum_exp 位 = Part D req_sum_exp 闭名） *)
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
   三步链（清单结论消费面；minus → req_minus unfold 后直配） *)
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
(* Part F：GRPONoDup R 侧余 4 件（Id Module UpGRPO219 L113533-113860） *)
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

(* Id UpGRPO219.grpo_count_one L113775：结论 @Id nat 原样，count 机跨接口复用（1 行组装） *)
Theorem req_grpo_count_one : forall (l : list rGroup) (Hnd : UpGRPO219.nodup_g rGroup l)
    (j : rGroup), InT j l -> Id (UpGRPO219.count_g rGroup rgrp_eq_dec j l) (Datatypes.S O).
Proof.
  intros l Hnd j Hin. exact (UpGRPO219.grpo_count_one rGroup rgrp_eq_dec l Hnd j Hin).
Qed.

(* Id list_sum_g_zero_fn L113609（归纳 + plus_zero 换形；premise InT 位原样） *)
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
   G 位 = reqd_of_nat (length rgroup_enum)，G_pos 假设位同构） *)
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
(* 零记录消费（Differentiable 系 (c) 桥C2 随波4）；语句位 minus →  *)
(* req_minus（登记表 1）；log 消费位前提化 + 同位假设位（登记表 2）。   *)

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
   结构：Hv 换形 → 四项平方展开 → h·u 换位 → 二倍槽收拢 → plus_assoc
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
   同位假设位（登记表 2）：setoid 接口无 log_div 字段，UpReqAlgebra
   MinP 卡跨席消费正路 (a)），End 时入闭包签名，非公理。 *)
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
